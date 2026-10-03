"""Build and audit the proved prefix; completion is an explicit separate gate."""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
WORKSPACE = ROOT.parents[1]
DEFAULT_REPORT = ROOT / ".lake/verification"
TRUSTED = {"propext", "Classical.choice", "Quot.sound"}
FINAL = {"exact_even_cycle_theorem", "exact_power_of_two_corollary"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-complete", action="store_true")
    parser.add_argument("--clean", action="store_true", help="Remove only this project's build tree first.")
    parser.add_argument("--report-dir", type=Path, default=DEFAULT_REPORT)
    args = parser.parse_args()
    REPORT = args.report_dir.resolve()
    REPORT.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    if os.name == "nt":
        env.setdefault("ELAN_HOME", str(Path.home() / ".elan"))

    def run(command, log):
        result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                encoding="utf-8", errors="replace", capture_output=True)
        output = result.stdout + result.stderr
        (REPORT / log).write_text(output, encoding="utf-8")
        if result.returncode:
            print("\n".join(line for line in output.splitlines()
                            if not line.startswith("trace: .> LEAN_PATH=")))
        return result.returncode, output

    if args.clean:
        build = ROOT / ".lake/build"
        resolved = build.resolve()
        if not resolved.is_relative_to(ROOT.resolve()) or resolved.name != "build":
            raise RuntimeError("Refusing to remove a build tree outside the project: " + str(resolved))
        print("Clean project build tree: " + str(resolved), flush=True)
        if build.exists():
            shutil.rmtree(build)
    code, _ = run(["lake", "build"], "build.log")
    if code:
        return code
    files = sorted((ROOT / "Girth").glob("*.lean")) + [ROOT / "Girth.lean"]
    names = []
    forbidden = []
    for path in files:
        source = path.read_text(encoding="utf-8")
        names.extend(re.findall(r"(?m)^theorem\s+([A-Za-z_][A-Za-z_0-9]*)", source))
        # This source scan supplements (and never replaces) Lean's dependency audit.
        if re.search(r"\b(sorry|admit)\b|(?m:^\s*axiom\s)", source):
            forbidden.append(str(path.relative_to(ROOT)))
    audit_source = ROOT / ".lake/Audit.lean"
    complete = FINAL.issubset(names)
    statement_gate = ("\nexample : GirthVerification.ExactEvenCycleTheorem := "
                      "GirthVerification.exact_even_cycle_theorem\n"
                      "example : GirthVerification.ExactPowerOfTwoCorollary := "
                      "GirthVerification.exact_power_of_two_corollary\n") if complete else ""
    audit_source.write_text("import Girth\n" + "\n".join(
        f"#print axioms GirthVerification.{name}" for name in names) +
        "\n#print GirthVerification.ExactEvenCycleTheorem\n"
        "#print GirthVerification.ExactPowerOfTwoCorollary\n" + statement_gate, encoding="utf-8")
    audit_code, output = run(["lake", "env", "lean", str(audit_source)], "axioms.log")
    axiom_rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
    clean_rows = re.findall(r"'([^']+)' does not depend on any axioms", output)
    unexpected = {}
    for name, axioms in axiom_rows:
        extra = sorted(set(a.strip() for a in axioms.split(",")) - TRUSTED)
        if extra:
            unexpected[name] = extra
    all_names = set(name for name, _ in axiom_rows) | set(clean_rows)
    missing_audits = sorted("GirthVerification." + name for name in names
                            if "GirthVerification." + name not in all_names)
    report = {
        "recorded_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "status": "COMPLETE_CANDIDATE" if complete else "PROVED_PREFIX_ONLY",
        "build_exit_code": code,
        "clean_project_build": args.clean,
        "audit_exit_code": audit_code,
        "theorems_audited": len(names),
        "trusted_foundations_allowed": sorted(TRUSTED),
        "unexpected_axioms": unexpected,
        "missing_axiom_outputs": missing_audits,
        "source_scan_findings": forbidden,
        "final_theorems_present": {name: name in names for name in sorted(FINAL)},
        "source_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in files},
        "dependencies": json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8")),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "limitations": ["A prefix audit is not verification of the main theorem.",
                        "The final release additionally requires a clean build and exact statement check."],
    }
    (REPORT / "verification.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in (
        "status", "theorems_audited", "unexpected_axioms", "missing_axiom_outputs",
        "source_scan_findings", "final_theorems_present")}, indent=2))
    if audit_code or unexpected or forbidden or missing_audits:
        return 1
    return 2 if args.require_complete and not complete else 0


if __name__ == "__main__":
    sys.exit(main())
