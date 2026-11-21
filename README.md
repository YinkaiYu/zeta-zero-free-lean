# A compact Lean 4 proof of the classical zero-free region for the Riemann zeta function

**Yin-Kai Yu (余荫铠)** · GPT-6.2 Astra · ChatGPT Desktop  
[研究说明（中文）](README.zh-CN.md) · [Paper (PDF)](paper/zero-free-region.pdf) · [LaTeX source](paper/zero-free-region.tex) · [Final Lean proof](Solution.lean) · [Official record](https://riemann.verifytask.cn/api/attempt/96295)

For every complex number $s\ne 1$, the proof establishes

$$
\operatorname{Re}(s) \geq 1-\frac{2^{-20}}{\log(|\operatorname{Im}(s)|+2)}
\quad\Longrightarrow\quad \zeta(s)\ne 0.
$$

Submission **#96295** held the Core 1 record in the 22 November 2026, 06:32:56 UTC+8 leaderboard snapshot. Its single Lean file uses **2,388 normalized leaderboard tokens**, down **88.97%** from the 21-file, 21,641-token reference closure. Playground awarded **65.873483**. The archive contains the five submitted sources spanning our four record improvements. [Challenge statement](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729) · [Progress curve](https://riemann.verifytask.cn/) · [Archived measurements](records/results.json)

## The argument

1. **Remove the pole once.** Let $F$ be the entire extension of $(s-1)\zeta(s)$. Abel summation with the fractional part of $u$ gives a single Mellin remainder $E(s)$. For $\operatorname{Re}(s)>0$, $F(s)=s(1-(s-1)E(s))$. Bounding that same integral gives a quadratic upper bound for $|F|$ and a lower bound for the height of a hypothetical zero.
2. **Keep the contribution of one prescribed zero.** On a disk with relative growth budget $B$, factoring out a nearby zero by Mathlib's differentiable divided difference cuts the budget to $B/2$. An induction starting at an integer $n>2B$ then needs only linear arithmetic for descent. In the other branch, normalize a primitive of $f'/f$ at zero. Borel–Carathéodory on radius $1/6$ and Cauchy's estimate on the circle of radius $1/12$ give $24(\log B+1)$.
3. **Put the three heights into the same lemma.** Apply the disk bound to translates of $F$ at heights $0,t,2t$. Only the middle height carries the prescribed zero. The modulus-one Dirichlet character product controls the weighted sum of logarithms. The independent identity $3+4\cos\theta+\cos(2\theta)=2(1+\cos\theta)^2$ controls the weighted von Mangoldt series. The residual reciprocal-distance term contradicts the available growth when $c=2^{-20}$. The paper works out the constants. [Analytic estimates](paper/analysis.tex) · [Three-height calculation](paper/three-heights.tex)

## The four patches

“Own reduction” compares adjacent archived sources. “Record gain” compares each source with the leading Core 1 proof at the moment of submission.

| Full patch | Result in tokens | Own reduction | Record gain | Change to inspect |
|---|---:|---:|---:|---|
| [#96267 → #96281](diffs/96267-to-96281.diff) | 2,892 | 236 | 132 | Define the real part of the von Mangoldt series directly. Combine its three sums before invoking positivity. |
| [#96281 → #96285](diffs/96281-to-96285.diff) | 2,724 | 168 | 38 | Replace a variable-radius derivative argument with Cauchy's estimate on one circle. Rewrite the same complex logarithmic derivative at all three centers. |
| [#96285 → #96293](diffs/96285-to-96293.diff) | 2,424 | 300 | 262 | Refactor the divided-difference induction around $n>2B$ and replace the parameter-dependent growth estimate with an intrinsic quadratic bound. |
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
