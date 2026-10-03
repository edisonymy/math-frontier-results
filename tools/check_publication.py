"""Check the selected public Git index, not the parent research workspace."""
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
actual = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], cwd=ROOT, text=True).strip()).resolve()
if actual != ROOT:
    raise SystemExit('Expected the standalone public repository, not a parent checkout')
files = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode('utf-8').split('\0')
roots = {'README.md', 'PROCESS.md', '.gitignore', '.gitattributes'}
prefixes = ('results/', 'templates/', 'tools/')
extensions = {'.md', '.txt', '.tex', '.bib', '.json', '.py', '.csv', '.cff', '.pdf'}
patterns = [
    ('local user path', r'(?i)(?:[A-Z]:[\\/]Users[\\/]|/Users/|/home/)'),
    ('internal operational path', r'(?i)(?:private_campaign_packets[\\/]|output/browser-runtime[\\/]|\.claude[\\/]|\.codex[\\/])'),
    ('credential-like token', r'\b(?:gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|sk-[A-Za-z0-9_-]{20,})\b'),
]
errors = []
count = 0
for name in filter(None, files):
    count += 1
    file = ROOT / name
    if (name not in roots and (not name.startswith(prefixes) or file.suffix.lower() not in extensions)):
        errors.append(name + ': outside the public file selection')
        continue
    if not file.resolve().is_relative_to(ROOT) or file.is_symlink():
        errors.append(name + ': linked file outside the public export')
        continue
    if file.suffix.lower() == '.pdf':
        continue  # The release owner inspects the rendered PDF, not a text scanner.
    data = subprocess.check_output(['git', 'show', ':' + name], cwd=ROOT)
    try:
        text = data.decode('utf-8-sig')
    except UnicodeDecodeError:
        errors.append(name + ': expected UTF-8 text')
        continue
    # The scanner's own regex definitions are not manuscript contents.
    if name != 'tools/check_publication.py':
        for label, pattern in patterns:
            if re.search(pattern, text):
                errors.append(name + ': ' + label)
        if file.suffix == '.md':
            for target in re.findall(r'\]\(([^)]+)\)', text):
                target = target.split('#', 1)[0]
                if not target or re.match(r'^[a-zA-Z][a-zA-Z0-9+.-]*:', target):
                    continue
                destination = (file.parent / target).resolve()
                if not destination.is_relative_to(ROOT) or not destination.exists():
                    errors.append(name + ': broken or non-public relative link')
if errors:
    raise SystemExit('\n'.join(errors))
print(f'PASS: {count} selected public files; no detected internal paths, credential patterns or broken relative links. Mathematical review remains the principal\'s responsibility.')
