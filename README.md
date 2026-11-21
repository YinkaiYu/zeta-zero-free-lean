# A compact Lean 4 proof of the classical zero-free region for the Riemann zeta function

**Yin-Kai Yu (余荫铠)** · GPT-6.2 Astra · ChatGPT Desktop  
[研究说明（中文）](README.zh-CN.md) · [Paper (PDF)](paper/zero-free-region.pdf) · [LaTeX source](paper/zero-free-region.tex) · [Final Lean proof](Solution.lean) · [Official record](https://riemann.verifytask.cn/api/attempt/96295)

## The problem and the competition

The Riemann zeta function connects complex analysis with the distribution of primes. The classical zero-free region theorem gives a strip along the line $`\operatorname{Re}(s)=1`$ in which the function has no zeros. Its width decreases slowly as the absolute value of the imaginary part grows. Such estimates help bound the error in counting primes. The Riemann hypothesis makes a stronger prediction, placing every nontrivial zero on $`\operatorname{Re}(s)=\tfrac12`$. This archive gives an unconditional proof of the classical region.

The Agentic Science Challenge selected five theorems from Levent Alpöge’s formalization as separate competition problems. Core 1 is the classical zero-free region. Entrants must prove the same Lean 4 statement using a fixed version of Mathlib, Lean’s mathematics library. The Lean kernel checks the proof. The competition then measures its source length in normalized tokens. A Core 1 record means a shorter verified proof of this particular theorem. The green progress curve combines the best results across all five problems.

## The explicit bound

For every complex number $`s=\sigma+it`$ with $`s\ne1`$, the proof establishes

```math
\sigma \ge 1-\frac{2^{-20}}{\log(|t|+2)} \quad\Longrightarrow\quad \zeta(s)\ne 0.
```

Submission **#96295** held the Core 1 record in the 22 November 2026, 06:32:56 UTC+8 leaderboard snapshot. Its single Lean file uses **2,388 normalized leaderboard tokens**, down **88.97%** from the 21-file, 21,641-token reference closure. Playground awarded **65.873483**. The archive contains the five submitted sources spanning our four record improvements. [Challenge statement](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729) · [Progress curve](https://riemann.verifytask.cn/) · [Archived measurements](records/results.json)

## Where the reference proof spends its source

The reference theorem, `Formalism.ZF.zeroFreeRegion`, assembles its local Landau estimate as `localZeroExpansionOfFactorization zeroFactorization logDerivBoundOnBall`. The first input carries enough information to recover every zero and its order. In `ZeroFactor.lean`, `exists_factorization_of_sum_order` builds a factorization with a holomorphic remainder. In `LandauLocalOf.lean`, `hasDerivAt_prod_sub_pow` differentiates the finite product of powers of w − ρ. Its logarithmic derivative yields a sum of reciprocal distances. A separate estimate controls the zero-free factor. The eventual three-height contradiction uses one prescribed reciprocal distance and the sign of the other contributions. That observation lets us change what the local lemma must return. [Author’s source release](https://alpo.ge/remark.pdf) · [Challenge statement and baseline](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729)

## The local estimate and its three applications

**1. Retain the contribution the caller needs.** Let f be entire, with $`f(0)\ne0`$ and every zero in the closed left half-plane. Suppose $`|f(w)|\le B|f(0)|`$ on the closed disk of radius 1/2, so B ≥ 1. Take x = 0, or choose a zero ρ with $`|\rho|\le\tfrac16`$ and $`x\le-\operatorname{Re}(1/\rho)`$. The submitted lemma `ClassicalZFR.landau` proves

```math
x-\operatorname{Re}\!\left(\frac{f'(0)}{f(0)}\right)\le 24(\log B+1).
```

**2. Remove one zero.** Take g to be the divided difference of f at ρ. Mathlib’s `differentiableOn_dslope` gives differentiability even at ρ, and `sub_smul_dslope_of_zero` gives f(w) = (w − ρ)g(w). On the circle ∣u∣ = 1/2, the reverse triangle inequality gives $`|u-\rho|\ge\tfrac12-\tfrac16=\tfrac13\ge2|\rho|`$. Since $`|f(0)|=|\rho|\,|g(0)|`$, we obtain

```math
|g(u)|=\frac{|f(u)|}{|u-\rho|}\le\frac{B|\rho|\,|g(0)|}{2|\rho|}=\frac B2\,|g(0)|.
```

The maximum modulus principle extends the bound to the closed disk. Logarithmic differentiation gives $`\frac{f'(0)}{f(0)}=-\frac1\rho+\frac{g'(0)}{g(0)}`$. The condition on x cancels the removed term, so it suffices to apply the lemma recursively to g with zero weight. A repeated zero can be removed again. This handles multiplicities without carrying a finite product through the proof.

An earlier version chose n with $`B<2^n`$. The final code chooses a natural number $`n>2B`$. At n = m + 1, the facts B ≥ 1 and 2B < m + 1 imply B < m, precisely the recursive premise 2(B/2) < m. On return, log(B/2) ≤ log B finishes the bound. The source credits Pi’s public submission for this monotonicity step. [Final disk lemma](Solution.lean#L75-L119) · [Induction diff](diffs/96285-to-96293.diff)

**3. Account for the constant 24.** When no witness exists, x = 0. Any zero inside the inner disk would have −Re(1/ρ) ≥ 0 and would supply a witness. Thus f′/f has a primitive G there with G(0) = 0. From f = f(0) exp(G) we get Re G ≤ log B. Put A = log B + 1. Apply `borelCaratheodory_zero` on the disk of radius 1/6 and evaluate on the circle of radius 1/12 to obtain ∣G∣ ≤ 2A. Cauchy’s derivative bound then gives $`\left|\frac{f'(0)}{f(0)}\right|=|G'(0)|\le\frac{2A}{1/12}=24A`$. Lean supplies that last step as `norm_deriv_le_of_forall_mem_sphere_norm_le`. [Fixed-circle estimate diff](diffs/96281-to-96285.diff)

**4. Use the lemma at three heights.** Let F be the entire extension of (s − 1)ζ(s). The same Abel–Mellin remainder gives quadratic growth and a lower bound ∣t∣ ≥ 1/2 for the height of a hypothetical zero β + it in the claimed region. Put $`L=\log(|t|+2)`$, $`d=2^{-20}/L`$ and a = β + 5d. Translate F to a, a + it and a + 2it. The middle translate has a zero at −5d and contributes 4/(5d) after weighting. The real pole term contributes at most 3/(4d), leaving 1/(20d).

Two positivity estimates control the remaining terms. A product inequality for the character of modulus one bounds the weighted logarithms of the three center values from below. For the logarithmic derivatives, $`3+4\cos\theta+\cos(2\theta)=2(1+\cos\theta)^2`$ and the nonnegative von Mangoldt coefficients give a nonnegative weighted series. Substitution requires $`(2^{20}-11520)L<103860`$, while $`L\ge\log 2>\tfrac12`$ makes the left side greater than 518528. This proves the stated region. [Full calculation](paper/three-heights.tex)

## Accounting for the 88.97% reduction

The reference closure contains 21 Lean files and 21,641 normalized tokens. Our first archived comparison, submission 96267, already implements the entire-function and single-zero route in one file of 3,128 tokens, a difference of 18,513. The four subsequent patches save 236, 168, 300 and 36 more, totaling 740. Together the two intervals account for 19,253 of 21,641 tokens, or **88.97%**. The first comparison measures two complete implementations. The four later reductions can each be replayed from a submitted source, and each saving belongs to its whole patch. [Measurements and source hashes](records/results.json)

## The four patches

“Own reduction” compares adjacent archived sources. “Record gain” compares each source with the leading Core 1 proof at the moment of submission.

| Full patch | Result in tokens | Own reduction | Record gain | Change to inspect |
|---|---:|---:|---:|---|
| [#96267 → #96281](diffs/96267-to-96281.diff) | 2,892 | 236 | 132 | Define the real part of the von Mangoldt series directly. Combine its three sums before invoking positivity. |
| [#96281 → #96285](diffs/96281-to-96285.diff) | 2,724 | 168 | 38 | Replace a variable-radius derivative argument with Cauchy's estimate on one circle. Rewrite the same complex logarithmic derivative at all three centers. |
| [#96285 → #96293](diffs/96285-to-96293.diff) | 2,424 | 300 | 262 | Refactor the divided-difference induction around $`n>2B`$ and replace the parameter-dependent growth estimate with an intrinsic quadratic bound. |
| [#96293 → #96295](diffs/96293-to-96295.diff) | 2,388 | 36 | 36 | Preserve the outer factor in partial summation, rewrite the halved budget in the induction hypothesis, and close the trigonometric square directly. |

Each row covers the entire patch. The paper traces individual replacements to the Mathlib and Lean declarations. The final row also advanced the pillar record while the five-pillar curve rounded to 41.61% on both sides. [Engineering details](paper/engineering.tex) · [All five source snapshots](snapshots/)

## Reproduce the results

The five tags from `attempt-96267` through `attempt-96295` contain the corresponding submitted proofs. Their Git timestamps date the archiving work. Competition submission times are preserved in the record data. [Browse the complete GitHub comparison](https://github.com/YinkaiYu/zeta-zero-free-lean/compare/attempt-96267...attempt-96295)

With [Lean's elan toolchain manager](https://github.com/leanprover/elan), Git and Python 3 installed, run these commands from a clone.

```sh
python tools/check_archive.py
lake exe cache get Mathlib.Analysis.Complex.HalfPlane Mathlib.Analysis.MellinTransform Mathlib.NumberTheory.LSeries.SumCoeff Mathlib.NumberTheory.LSeries.Nonvanishing Mathlib.NumberTheory.Harmonic.ZetaAsymp Mathlib.Analysis.Complex.BorelCaratheodory Mathlib.Analysis.Complex.HasPrimitives Mathlib.Analysis.Calculus.LogDeriv
lake build
lake env lean Audit.lean
lake env leanchecker Solution
```

The Python check independently counts the leaderboard tokens in these five files and applies all four unified diffs in sequence. The Lean commands use the locked Lean 4.34.1 and Mathlib revision. The audit checks the full challenge type and prints the axioms of `AlpogeRHCore1.zeroFreeRegion`. The expected list is `propext`, `Classical.choice`, `Quot.sound`. The final command independently replays the compiled solution. [Exact type check](Audit.lean) · [Dependency lock](lake-manifest.json)

To build the paper, run `pdflatex zero-free-region.tex` twice from `paper/`. The release includes the typeset PDF. Citation metadata are available in [CITATION.cff](CITATION.cff).

## Sources and credit

The challenge supplies Levent Alpöge's reference theorem and its closure. The classical argument uses the de la Vallée Poussin weights. The formalization draws on Mathlib's Mellin transform, divided differences, Borel–Carathéodory inequality and Dirichlet series. The submitted source credits Pi's #96263 for the monotonicity step after halving the growth budget. [Challenge](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729) · [Pinned Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612) · [Pi's submission](https://riemann.verifytask.cn/api/attempt/96263)
