# 黎曼 ζ 函数经典无零点区的紧凑 Lean 4 证明

**Yin-Kai Yu (余荫铠)** · GPT-6.2 Astra · ChatGPT Desktop  
[英文论文 PDF](paper/zero-free-region.pdf) · [论文 LaTeX 源码](paper/zero-free-region.tex) · [最终 Lean 证明](Solution.lean) · [赛事提交 #96295](https://riemann.verifytask.cn/api/attempt/96295)

这份证明给出了一个显式常数。对任意复数 $s=\sigma+it\ne1$，

$$
\sigma\ge 1-\frac{2^{-20}}{\log(|t|+2)}
\quad\Longrightarrow\quad\zeta(s)\ne0.
$$

这是 Agentic Science Challenge 的第一项核心支柱。赛事参考证明的依赖闭包有 21 个 Lean 文件、21,641 个规范化词元。2026 年 11 月 22 日北京时间 06:32:56 的公开榜单快照中，**#96295 以单文件 2,388 词元位居 Core 1 第一，相对基线压缩 88.97%，正式得分 65.873483**。仓库收录起始对照版和四个刷新纪录的提交，每份源码均从对应的实际上传包中提取。[官方题面](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729) · [赛事曲线](https://riemann.verifytask.cn/) · [带时间和来源的成绩记录](records/results.json)

## 证明为什么能压短

**先统一三个高度上的函数。** 取 $F$ 为 $(s-1)\zeta(s)$ 的整函数延拓。Abel 求和给出 $F(s)=s(1-(s-1)E(s))$，其中 $E(s)$ 是由小数部分构造的 Mellin 余项。同一个余项估计可以推出两个结论：半平面上的二次增长界，以及假想零点的虚部下界。有了后者，三个高度中两个非实中心的极点项都有了显式上界。[解析推导](paper/analysis.tex)

**让圆盘引理记住一个指定零点。** 当附近有合适的零点 $\rho$，用 Mathlib 的可微差商把 $f$ 写成 $(w-\rho)g(w)$。在半径 $1/2$ 的边界比较增长量，新函数的相对增长界从 $B$ 降到 $B/2$。取自然数 $n>2B$ 作归纳，下降条件可以直接交给线性算术。在无零点分支，先取 $f'/f$ 的原函数，再用 Borel–Carathéodory 和 Cauchy 导数估计。半径 $1/12$ 的圆上有 $|g|\le 2(\log B+1)$，除以半径就得到常数 $24$。这一步用一个标准库圆周估计替代了围绕原点构造邻域界的证明。[引理与 Mathlib 替代](paper/engineering.tex)

**给同一条不等式配上权重 $3,4,1$。** 在高度 $0,t,2t$ 同时使用圆盘引理。中间高度保留假想零点提供的距离倒数，另外两处取零权重见证。模一特征的 $L$ 函数乘积下界控制三个中心的函数值，恒等式 $3+4\cos\theta+\cos(2\theta)=2(1+\cos\theta)^2$ 控制 von Mangoldt 级数的符号。两次正性估计合在一起，留下显式常数 $2^{-20}$ 所需的数值矛盾。[三高度推导与常数核算](paper/three-heights.tex)

## 每次突破对应哪一段改动

| 完整 Lean 差异 | 结果词元 | 比本组上一份少 | 比当时榜首少 | 主要改动 |
|---|---:|---:|---:|---|
| [#96267 → #96281](diffs/96267-to-96281.diff) | 2,892 | 236 | 132 | 直接以 von Mangoldt 级数的实部组织三个可和性证明 |
| [#96281 → #96285](diffs/96281-to-96285.diff) | 2,724 | 168 | 38 | 在固定圆周上用 Cauchy 导数估计，统一三处对数导数的复数恒等式 |
| [#96285 → #96293](diffs/96285-to-96293.diff) | 2,424 | 300 | 262 | 用 $n>2B$ 重写差商归纳，把依赖外部参数的增长估计改成内在二次界 |
| [#96293 → #96295](diffs/96293-to-96295.diff) | 2,388 | 36 | 36 | 匹配 Abel 求和的因式形式，在归纳假设内改写增长界，用平方非负直接收尾 |

每一行的节省量对应整份差异。前三次突破均推动五项合计曲线的两位小数读数，最后一次把 Core 1 纪录再降了 36 个词元，合计曲线前后均显示 41.61%。[原始版本](snapshots/) · [成绩及 SHA-256](records/results.json)

## 本地复核

五个 Git 标签分别保存五次提交的证明。Git 提交时间是本次建档时间，实际参赛提交时间见成绩记录。[在 GitHub 逐行对照首末两版](https://github.com/YinkaiYu/zeta-zero-free-lean/compare/attempt-96267...attempt-96295)

安装 Git、Python 3 和 [Lean 工具链管理器 elan](https://github.com/leanprover/elan)，从仓库根目录执行：

```sh
python tools/check_archive.py
lake exe cache get Mathlib.Analysis.Complex.HalfPlane Mathlib.Analysis.MellinTransform Mathlib.NumberTheory.LSeries.SumCoeff Mathlib.NumberTheory.LSeries.Nonvanishing Mathlib.NumberTheory.Harmonic.ZetaAsymp Mathlib.Analysis.Complex.BorelCaratheodory Mathlib.Analysis.Complex.HasPrimitives Mathlib.Analysis.Calculus.LogDeriv
lake build
lake env lean Audit.lean
lake env leanchecker Solution
```

第一条命令会重算五份源码的词元数和 SHA-256，并顺序应用四份补丁，验证每一步都能逐字节还原下一次提交。工程固定使用 Lean 4.34.1 和题目指定的 Mathlib 修订。类型检查文件核对完整定理陈述并列出依赖公理，结果为 `propext`、`Classical.choice`、`Quot.sound`。最后一条命令重放已编译的证明。[类型检查](Audit.lean) · [依赖版本](lake-manifest.json)

这条路线继承 de la Vallée Poussin 的经典三高度论证。赛事参考形式化来自 Levent Alpöge。差商剥离后用单调性放宽增长界的一步，在实际提交的源码中已注明参考 Pi 的公开提交 #96263。论文给出了每项工程改写对应的数学式、Mathlib 声明和完整差异。[Alpöge 的源码说明](https://alpo.ge/remark.pdf) · [Pi 的公开提交](https://riemann.verifytask.cn/api/attempt/96263) · [固定版本的 Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612)
