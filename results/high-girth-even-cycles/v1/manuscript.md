# Exact even cycle lengths in high-girth graphs of minimum degree three

Version: v1, prepared 3 October 2026.  
Status: **unrefereed preprint; AI-assisted proof with internal independent AI checks**.  
Prepared by the Math Frontier research campaign, directed and maintained by Edison Yi.  
The release record, when published, supplies the public disclosure timestamp.

## Abstract

Put $a=\log(20/19)$, where logarithms are natural. We give a complete
argument that there is an absolute $n_0$ such that every finite simple graph
$G$ with $n\ge n_0$ vertices, minimum degree at least three and girth at
least $40\log\log n$ contains a simple cycle of every even integer length

$$
\frac{4\log N}{a}\le L\le\frac{8\log N}{a},
\qquad N=2|E(G)|.
$$

In particular it contains a cycle whose length is a power of two. No
regularity, connectivity, upper degree bound, expansion or mixing assumption
is imposed. The proof uses edge reversal to control the real outer spectrum
of the non-backtracking transition matrix, a dimension-independent remainder
estimate, and a weighted count of repeated vertices. The size threshold is
not optimized, and this result does not resolve the Erdős–Gyárfás conjecture.

## 1. Statement, conventions and prior work

All graphs are finite, simple and undirected. A cycle means a vertex-simple
cycle. The girth is the length of a shortest cycle. The adjoint of a matrix
is denoted by $^{*}$, its Euclidean operator norm by $\|\cdot\|$, and
$A\preceq B$ means that $B-A$ is positive semidefinite. All logarithms
are natural.

**Theorem 1.** There is an absolute integer $n_0$ such that, if
$n=|V(G)|\ge n_0$, $\delta(G)\ge3$, and
$\operatorname{girth}(G)\ge40\log\log n$, then $G$ has a simple cycle
of each even integer length in

$$
I_G=\left[\frac{4\log(2|E(G)|)}{\log(20/19)},
          \frac{8\log(2|E(G)|)}{\log(20/19)}\right].
\tag{1}
$$

**Corollary.** Under these hypotheses, $G$ has a simple cycle of length
$2^k$ for some integer $k\ge2$.

Indeed, the first power of two at least the left endpoint of (1) is at most
twice that endpoint and hence belongs to the interval. For sufficiently large
$n$, it is at least four.

The Erdős–Gyárfás conjecture asks for this corollary under just
$\delta(G)\ge3$. The additional girth and size hypotheses in Theorem 1
are essential to the argument given here; no reduction removing them is claimed.

Sudakov and Verstraëte [SV] relate girth and average degree to large sets of
cycle lengths. Liu and Montgomery [LM] prove, in particular, that sufficiently
large average degree forces a power-of-two cycle. Friedman and Krivelevich
[FK] study cycle-length distributions under expansion assumptions. These are
the closest general cycle-length directions considered in our literature
comparison. Kempton [K] develops weighted Ihara identities for
non-backtracking random walks; the use of directed edges, reversal, spectral
information and trace identities has substantial prior history.

The contribution proposed here is the complete implication at minimum degree
three under the girth hypothesis of Theorem 1, including the treatment of
irregular degrees and the conversion of closed walks to simple cycles.
Individual spectral identities are not claimed to be new. Our literature
search did not identify a published theorem implying this exact statement,
but this is not a claim of exhaustive novelty verification. Related public
evaluation requests [P71, P73] impose expansion assumptions and are not
independently reviewed in this note. No precedence over those or other works
is asserted.

## 2. Reversal and the non-backtracking operator

Let $d_v=d_G(v)$, $q_v=d_v-1\ge2$, and let $\vec E$ be the set of
$N=2|E(G)|$ directed edges. Define

$$
P_{(u,v),(v,w)}=\frac1{q_v}\quad(w\ne u),
$$

with all other entries zero. Each row sums to one. The column indexed by
$(v,w)$ has exactly $q_v$ predecessors, all with the same denominator,
so each column also sums to one. In particular $\|P\|\le1$: by the
weighted Cauchy–Schwarz inequality,
$\sum_e |(Px)_e|^2\le\sum_{e,f}P_{ef}|x_f|^2=\|x\|^2$.

Let $J$ be the permutation matrix reversing directed edges. Thus
$J=J^*=J^{-1}$. The matrix

$$
H=PJ=H^*,\qquad P=HJ,\qquad P^*=JPJ
\tag{2}
$$

is block diagonal on the directed edges entering each vertex. At vertex
$v$ its block has zero diagonal and off-diagonal entries $1/q_v$.
Its eigenvalues are $1$ on the constant vector and $-1/q_v$ on the
orthogonal complement. In particular $H$ is invertible, and

$$
H^2\preceq\tfrac12(I+H),\qquad
H^{-2}\succeq2I-H^{-1},\qquad
P^*P\preceq\tfrac12(I+JP).
\tag{3}
$$

The first two inequalities follow on the displayed block eigenspaces:
$b^2\le(1-b)/2$ for $0\le b\le1/2$, and
$q_v^2\ge q_v+2$. Conjugating the first by $J$ gives the third.

## 3. The outer spectrum and a uniform frame bound

Suppose $Pf=zf$ with $f\ne0$. Then

$$
Jf=zH^{-1}f.
\tag{4}
$$

Let $A$ be the squared norm of the projection of $f$ onto the positive
eigenspaces of $H$, and let $b_v$ be the squared norm of its projection
onto the negative eigenspace in the block at $v$.

If $z$ is nonreal, both quadratic forms $f^*Jf$ and
$f^*H^{-1}f$ are real, so (4) gives
$f^*H^{-1}f=f^*Jf=0$. Thus $A=\sum_v q_v b_v$. Taking norms in (4)
yields

$$
|z|^2=
\frac{\sum_v(q_v+1)b_v}{\sum_v q_v(q_v+1)b_v}
\le\frac12.
\tag{5}
$$

The denominator is positive: otherwise all $b_v$, and then $A$,
would vanish. Hence all eigenvalues outside the disc of radius
$1/\sqrt2$ are real.

Now let $z$ be real with $1/\sqrt2<|z|<1$. Put
$s=f^*H^{-1}f$. Equation (4) gives

$$
(1-z^2)A=\sum_v(z^2q_v^2-1)b_v,
\qquad
(1-z^2)s=\sum_v(q_v+1)(z^2q_v-1)b_v.
$$

Also $(1-z^2)\|f\|^2=z^2\sum_v(q_v^2-1)b_v$. Termwise comparison,
using $q_v\ge2$, therefore gives

$$
\frac{s}{\|f\|^2}\ge\frac{2z^2-1}{z^2},\qquad
\operatorname{sign}(z)f^*Jf\ge\gamma(|z|)\|f\|^2,
\qquad \gamma(t)=\frac{2t^2-1}{t}.
\tag{6}
$$

For example, the individual ratio in this comparison is
$(q_vz^2-1)/((q_v-1)z^2)$, minimized at $q_v=2$.
If $|z|=1$, the norm equation forces every $b_v=0$, and (4) again
gives (6).

Since $P^*J=JP$, eigenspaces at distinct real eigenvalues are
$J$-orthogonal. Their $J$-forms are definite by (6). Each real
eigenvalue $|z|>1/\sqrt2$ is semisimple: a Jordan chain
$(P-zI)f_1=f_0$ would imply both
$f_0^*J(P-zI)f_1=0$ and $f_0^*Jf_0\ne0$.

Choose a basis $f_j$ for these eigenspaces satisfying
$f_i^*Jf_j=\operatorname{sign}(z_j)\delta_{ij}$. The spectral projector
for an outer eigenvalue is

$$
\Pi_z=\operatorname{sign}(z)\sum_{j:z_j=z}f_j f_j^*J.
\tag{7}
$$

It is the identity on that eigenspace and annihilates every other generalized
eigenspace. For the latter assertion use the left eigenvector $f_j^*J$
and a power of $P-wI$ when $w\ne z$.

Fix $1/\sqrt2<c<1$, and first take just the eigenvalues $z>c$, or just
the eigenvalues $z<-c$. Let $F$ have the corresponding vectors as
columns, $Z=\operatorname{diag}(|z_j|)$, and $G=F^*F$. Within this
single sign class, (4) gives

$$
F^*H^{-1}F=Z^{-1},\qquad
G=ZF^*H^{-2}FZ.
$$

Using (3) and rearranging,

$$
G\succeq2ZGZ-Z,
\qquad
G\preceq\tfrac12 Z^{-1}GZ^{-1}+\tfrac12 Z^{-1}.
$$

Iteration is valid because $\|Z^{-1}/\sqrt2\|\le1/(\sqrt2 c)<1$.
The remainder tends to zero and the geometric series gives

$$
G\preceq Z(2Z^2-I)^{-1}\preceq\gamma(c)^{-1}I,
\qquad FF^*\preceq\gamma(c)^{-1}I.
\tag{8}
$$

This bound holds separately for the two signs. Consequently, for nonreal
$w$, (7) and (8) imply

$$
\left\|\sum_{|z|>c}\frac{\Pi_z}{w-z}\right\|
\le\frac{2}{\gamma(c)|\operatorname{Im}w|}.
\tag{9}
$$

The estimate controls the full frame; summing individual projector norms
instead would lose a factor depending on the graph size.

## 4. A dimension-independent bound for the remaining powers

Eigenvalue containment does not by itself bound powers of a nonnormal
matrix. We supply the required estimate explicitly.

For nonreal $w$ with $|w|>1/\sqrt2$, take $\|x\|=1$,
$y=(P-wI)x$, and $e=\|y\|$. Since $x^*JPx$ is real,

$$
|x^*Jx|\le\frac{e}{|\operatorname{Im}w|},\qquad
x^*JPx\le\left(\frac{|w|}{|\operatorname{Im}w|}+1\right)e.
$$

Use (3) and $\|Px\|^2\ge|w|^2-2|w|e$ to obtain

$$
\|(wI-P)^{-1}\|
\le\frac{2|w|+\tfrac12+|w|/(2|\operatorname{Im}w|)}{|w|^2-\tfrac12}.
\tag{10}
$$

The inverse exists by (5). On $h\le|w|\le2$, $h>1/\sqrt2$, the
right side is at most $12/((h^2-1/2)|\operatorname{Im}w|)$.

Define

$$
E_c=I-\sum_{|z|>c}\Pi_z,
\qquad
R_c(w)=(wI-P)^{-1}E_c
      =(wI-P)^{-1}-\sum_{|z|>c}\frac{\Pi_z}{w-z}.
$$

All removed poles cancel because they are semisimple. Thus $R_c$ is
analytic on $|w|>c$, including the removed real eigenvalues. Given
$c<b<1$, put

$$
\eta=\frac{b-c}{2},\quad h=\frac{b+c}{2},\quad
C(c,b)=\frac{12}{h^2-1/2}+\frac{2}{\gamma(c)}.
$$

Every closed disc of radius $\eta$ centred at a point $|z|=b$ lies
inside the analytic domain and has $h\le|w|<2$. Equations (9)–(10)
give $\|R_c(w)\|\le C(c,b)/|\operatorname{Im}w|$ at its nonreal points.

To remove the apparent real-axis singularity, fix unit vectors $u,v$
and apply the mean-value inequality for the subharmonic function
$\log|u^*R_c(w)v|$ on that disc. For real $y$,

$$
\frac1{2\pi}\int_0^{2\pi}\log|y+\eta\sin\theta|\,d\theta
\ge\log(\eta/2).
\tag{11}
$$

For completeness, multiply
$y+\eta(\zeta-\zeta^{-1})/(2i)$ by $\zeta$ on $|\zeta|=1$.
The resulting quadratic has leading coefficient of modulus $\eta/2$.
Factoring the quadratic and using the scalar Jensen formula gives (11);
each root contributes $\log\max(1,|\alpha|)\ge0$. Zeros on the circle
have integrable logarithmic singularities. The same inequality follows by
a limit from circles avoiding those zeros.

It follows that
$\log|u^*R_c(z)v|\le\log(2C(c,b)/\eta)$.
If the scalar function vanishes identically the bound is immediate.
Taking the supremum over $u,v$ and then using the matrix Cauchy integral
on $|z|=b$ proves, for every integer $t\ge0$,

$$
\|P^tE_c\|\le K(c,b)b^t,
\qquad K(c,b)=\frac{2bC(c,b)}{\eta}.
\tag{12}
$$

The contour encloses the spectrum on the range of $E_c$, so this argument
includes any Jordan blocks there. No diagonalizability of that restriction
is assumed.

## 5. Return weights and two separated cutoffs

Let $U_v$ be the indicator of directed edges leaving $v$. For
$t\ge1$, let $R_t(v)$ be the total weight of internally
non-backtracking closed walks of length $t$ starting at $v$, where
the weight of $v=v_0,v_1,\ldots,v_t=v$ is
$\prod_{i=0}^{t-1}q_{v_i}^{-1}$. Non-backtracking is required at the
internal positions; reversal at the closing seam is allowed. Exactly

$$
R_t(v)=q_v^{-1}U_v^*P^{t-1}JU_v.
\tag{13}
$$

The initial weight is $1/q_v$, not $1/d_v$. Such a walk has a simple
cycle as a subwalk, so $R_t(v)=0$ when $t<\operatorname{girth}(G)$.

For each outer eigenvector define
$\omega_{vj}=|U_v^*f_j|^2/(q_v|z_j|)\ge0$. Equations (7), (12) and
(13) imply, at any cutoff $c<b$,

$$
R_t(v)=\sum_{|z_j|>c}\operatorname{sign}(z_j)^t|z_j|^t\omega_{vj}+e_t(v),
\qquad |e_t(v)|\le E(c,b)b^t,
\qquad E(c,b)=\frac{3C(c,b)}{\eta}.
\tag{14}
$$

Indeed $\|U_v\|^2/q_v=d_v/q_v\le3/2$, and
$(3/2)K(c,b)b^{t-1}=E(c,b)b^t$.

Fix

$$
c_0=\frac34,\quad b_0=\frac45,\quad r=\frac9{10},\quad\rho=\frac{19}{20},
\qquad E_0=E(c_0,b_0),\quad E_1=E(r,\rho).
$$

Let $g\ge3$ be an integer lower bound for the girth, and let $j_0$
be the largest even integer strictly less than $g$. At time $j_0$
the left side of (14) is zero. All slow terms are nonnegative, and those
with $|z_j|>r$ form a subset. Hence

$$
\sum_{|z_j|>r}\omega_{vj}\le M_g:=E_0(8/9)^{j_0}.
\tag{15}
$$

The strict separation $b_0<r<\rho$ is used here. For the higher cutoff
put

$$
U_t(v)=\sum_{|z_j|>r}\omega_{vj}|z_j|^t,\qquad
S_t=\sum_{|z_j|>r}|z_j|^t.
$$

The eigenvalue one is present, so $S_t\ge1$. Formula (14) gives
$0\le R_t(v)\le U_t(v)+E_1\rho^t$. Also

$$
\sum_v\omega_{vj}\le C_w:=\frac{3}{2r\gamma(r)}=\frac{75}{31}.
\tag{16}
$$

To prove (16), the matrix $\sum_v U_vU_v^*/q_v$ is block diagonal on
outgoing edges and has norm at most $3/2$. Use
$\|f_j\|^2\le1/\gamma(r)$ from (8) and divide by $|z_j|\ge r$.

## 6. Controlling repeated vertices

Write $a_{ij}=\sum_v\omega_{vi}\omega_{vj}$. Every row and column sum
is at most $C_wM_g$, by (15)–(16). For $0<t<L$, weighted Young's
inequality $x^ty^{L-t}\le(t/L)x^L+(1-t/L)y^L$ gives

$$
\sum_v U_t(v)U_{L-t}(v)\le C_wM_gS_L.
\tag{17}
$$

There are at most $N$ slow modes, counting multiplicity. Hölder's
inequality gives
$S_{L-t}\le N^{t/L}S_L^{(L-t)/L}\le N^{t/L}S_L$, since $S_L\ge1$.
With $\kappa=\rho N^{1/L}$, expansion of the two return bounds yields

$$
\sum_vR_t(v)R_{L-t}(v)
\le C_wM_gS_L+C_wE_1S_L(\kappa^t+\kappa^{L-t})+nE_1^2\rho^L.
\tag{18}
$$

For even $L$, all real eigenvalues contribute nonnegative powers to the
trace. Each nonreal eigenvalue has modulus at most $1/\sqrt2$, by (5).
Thus

$$
\operatorname{tr}(P^L)\ge S_L-N2^{-L/2}.
\tag{19}
$$

This trace identity uses algebraic multiplicities and does not require a
diagonalizable matrix or a connected graph.

Let $w(C)=\prod_{v\in V(C)}q_v^{-1}$. The trace is the weighted sum of
cyclically non-backtracking closed words with a distinguished initial
directed edge. A simple undirected $L$-cycle contributes $2Lw(C)$.
A nonsimple word has at least one unordered pair of equal vertex positions.
Charge its weight to all such pairs. Cutting at a pair produces two
internally non-backtracking returns at the common vertex; their product
weight equals the original word weight. Forgetting the compatibility of
their closing seams only increases the count.

For a cyclic word with labelled positions, summing over a starting position
and a separation $1\le t<L$ counts each unordered pair twice. Rotation
preserves the word weight. Therefore the total weight of nonsimple words is
at most
$(L/2)\sum_{t=1}^{L-1}\sum_vR_t(v)R_{L-t}(v)$. We obtain

$$
\sum_{C:\,|C|=L}2Lw(C)
\ge\operatorname{tr}(P^L)
 -\frac L2\sum_{t=1}^{L-1}\sum_vR_t(v)R_{L-t}(v).
\tag{20}
$$

Only $g\le t\le L-g$ can contribute. In particular there are at most
$L$ terms. If $\kappa<1$, (18)–(20) give

$$
\sum_{C:\,|C|=L}2Lw(C)\ge S_L D,
\tag{21}
$$

where

$$
D=1-\frac{C_w}{2}L^2M_g
    -C_wE_1L\frac{\kappa^g}{1-\kappa}
    -\frac{nE_1^2}{2}L^2\rho^L-N2^{-L/2}.
\tag{22}
$$

We used $S_L\ge1$ to make the last two negative terms larger in
magnitude when factoring out $S_L$. Thus (21) remains valid even if
$D\le0$. When $D>0$, it proves the existence of an actual simple
$L$-cycle. Positivity of the trace alone would not do so.

## 7. Completion of the proof

Take $g=\lceil40\log\log n\rceil$ and $L$ in (1). Since
$a=-\log\rho$,

$$
\kappa\le\rho^{3/4}<1,\qquad \rho^L\le N^{-4}.
$$

Simplicity and minimum degree give $3n\le N<n^2$, so
$L=O(\log n)$, with absolute uniform constants. As
$j_0\ge g-2$, the first two error terms in (22) satisfy

$$
L^2M_g=O\big((\log n)^{2-40\log(9/8)}\big),
\qquad
L\kappa^g=O\big((\log n)^{1-30\log(20/19)}\big).
\tag{23}
$$

Both exponents are negative: $\log(9/8)>1/9$ and
$\log(20/19)>1/20$. The denominator $1-\kappa$ is bounded below
by $1-\rho^{3/4}>0$. The third error term in (22) is
$O((\log n)^2/n^3)$, and the last is at most $N^{-3}$, because
$1/\sqrt2<\rho$. Consequently $D=1-o(1)>0$ uniformly in all
admissible graphs and all even $L$ in (1). Increasing an absolute
$n_0$ if necessary also ensures $g\ge3$ and the upper endpoint of
(1) is less than $n$. This proves Theorem 1 and its corollary. $\square$

All constants in the intermediate estimates are explicit. Direct substitution
gives

$$
E_0=\frac{2535840}{161}<2^{14},\qquad
E_1=\frac{77569200}{17639}<2^{13},\qquad C_w=\frac{75}{31}<3.
$$

The theorem asserts existence of a finite absolute threshold; this version
does not certify a smallest numerical $n_0$. The slow decay in (23)
makes this a large-size theorem, not a practical small-graph test.

## 8. Scope, verification and attribution

This note proves only the statement in Section 1. It does not establish the
unrestricted Erdős–Gyárfás conjecture, a counterexample, a reduction of
arbitrary graphs to the present class, a theorem about odd cycle lengths,
or any sharpness claim for the constants. Edge-deletion extensions,
degree-two variants and graphs with overlapping short cycles are outside
this release.

The complete argument was developed within Math Frontier on 26 September
2026. Those private working dates are provenance, not public priority. The
present version reconstructs that argument without importing any unpublished
campaign lemma. The proof requires no graph census, solver certificate or
computer calculation as a premise.

Internal verification included an independent rederivation of the base
theorem by Claude Opus 5.5, a subsequent line-by-line Opus audit of the
original proof, and a separate ChatGPT Pro audit that checked the signed
spectral/frame/resolvent and collision prerequisites while reviewing a
different application. That Pro audit did not review every later extension.
These are AI checks, not independent human refereeing, proof-assistant
verification or journal acceptance. The release text was checked against
the original proof by the campaign's Primary assistant; it has not received
a separate external review. Readers should assess the complete proof above.

Edison Yi directed the research programme and maintains its public record.
AI systems performed the mathematical exploration, proof drafting and
substantive checking: OpenAI Codex/ChatGPT systems, including the Primary
assistant and a separate Pro audit, and Claude Opus 5.5. No human
line-by-line verification or external endorsement is claimed. Model-generated
audits are evidence about checking activity, not guarantees of correctness.

The account maintainer is credited for direction and curation; this statement
does not attribute a particular mathematical derivation to Edison personally.
No additional reuse licence for copyrightable text is granted in this version.
The mathematical claims and methods may be cited; any rights in text remain
subject to applicable law. No third-party manuscript text or figures are
reproduced.

Version history: v1 is the first selected public version of this theorem.
The repository release records its actual publication time. Later corrections
must identify the affected claim and retain the earlier version.

## References

- [SV] B. Sudakov and J. Verstraëte, *Cycle lengths in sparse graphs*,
  [arXiv:0707.2117](https://arxiv.org/abs/0707.2117). See also the authors'
  [addendum](https://people.math.ethz.ch/~sudakovb/addenda.pdf).
- [LM] H. Liu and R. Montgomery, *A solution to Erdős and Hajnal's odd cycle
  problem*, [arXiv:2010.15802](https://arxiv.org/abs/2010.15802).
- [FK] L. Friedman and M. Krivelevich, *Cycle lengths in expanding graphs*,
  [arXiv:1912.11011](https://arxiv.org/abs/1912.11011).
- [K] M. Kempton, *Non-backtracking random walks and a weighted Ihara's
  theorem*, [arXiv:1603.05553](https://arxiv.org/abs/1603.05553).
- [P71] GitHub user `thatnealpatel`, public evaluation request on high-girth expanders,
  [issue 71](https://github.com/thatnealpatel/proofs/issues/71), October 2026;
  an informal claim, not treated here as an accepted theorem.
- [P73] GitHub user `thatnealpatel`, public evaluation request on cubic expanders,
  [issue 73](https://github.com/thatnealpatel/proofs/issues/73), October 2026;
  an informal claim, not treated here as an accepted theorem.
