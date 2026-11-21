import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic

/- The entire completion of (s−1)ζ(s) allows all three logarithmic derivatives
   to be estimated with the same disk lemma, including the real center. -/
open Complex Metric Set Filter MeasureTheory Asymptotics Topology ArithmeticFunction
noncomputable section
namespace ClassicalZFR
variable {s z : ℂ} {R x : ℝ}
abbrev frac : ℝ → ℂ := ofReal ∘ Int.fract
def tail := (Ioi 1).indicator frac

lemma frac_bound x : ‖frac x‖ ≤ 1 := by
  simpa [frac,Int.abs_fract] using (Int.fract_lt_one x).le
abbrev remainder z := mellin tail (-z)
lemma tail_smooth : DifferentiableOn ℂ remainder {z | 0 < z.re} := by
  intro s hs
  refine (DifferentiableAt.comp (g := mellin tail) s ?_ differentiableAt_id.neg).differentiableWithinAt
  have hb x : ‖tail x‖ ≤ 1 := (norm_indicator_le_norm_self frac x).trans (frac_bound x)
  apply mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
  · exact (locallyIntegrableOn_const (1:ℂ)).mono (by unfold tail; fun_prop (disch := exact measurableSet_Ioi)) (by filter_upwards with x using by simpa using hb x)
  · exact isBigO_of_le _ fun x => by simpa using hb x
  · simpa
  · apply IsBigO.of_bound' 
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with x hx
    simp [tail, mem_Ioi, not_lt.mpr (mem_Iio.mp hx).le]
  · simp

abbrev integrand (s : ℂ) (x : ℝ) := (x:ℂ)^(-s-1) * frac x
lemma mellin_eq : remainder s = ∫ x in Ioi 1, integrand s x := by
  rw [remainder,mellin,tail,←indicator_smul,setIntegral_indicator measurableSet_Ioi]
  simp [integrand]

lemma entireFormula (hs : 0 < s.re) : riemannZeta₁ s = s * (1-(s-1)*remainder s) := by
  have hu (r:ℝ) := isOpen_lt (f:=fun _ : ℂ => r) continuous_const continuous_re
  apply (differentiable_riemannZeta₁.differentiableOn.analyticOnNhd (hu 0)).eqOn_of_preconnected_of_eventuallyEq
    (DifferentiableOn.analyticOnNhd (by have := tail_smooth; fun_prop) (hu 0))
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by norm_num) _ hs
  filter_upwards [(hu 1).mem_nhds (by norm_num : 1 < (2:ℂ).re)] with z hz
  have h := LSeries_eq_mul_integral' (1 : ℕ → ℂ) zero_le_one hz (by simp; rfl)
  simp [LSeries_one_eq_riemannZeta hz] at h
  have hf : IntegrableOn (integrand z) (Ioi 1) := (integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one).mul_bdd
    (by fun_prop : Measurable frac).aestronglyMeasurable (.of_forall frac_bound)
  have hi := integral_Ioi_cpow_of_lt (a := -z) (by simpa) zero_lt_one
  simp [← neg_sub z 1,neg_add_eq_sub,-neg_sub] at hi
  suffices riemannZeta z = z*(z-1)⁻¹ - z * remainder z by
    have hn : z ≠ 1 := by grind [one_re]
    grind [riemannZeta_eq_inv_sub_mul hn]
  rw [h, ← hi, mellin_eq, ← mul_sub, ← integral_sub
    (integrableOn_Ioi_cpow_of_lt (by simpa) zero_lt_one) hf]
  congr 1; refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hxC := ofReal_ne_zero.mpr hx0.ne'
  simp [integrand, frac, Int.fract, ← Int.natCast_floor_eq_floor hx0.le,
    show -1+-z = -z-1 by ring, cpow_sub _ _ hxC]; field [hxC]

lemma mellin_bound (hs : 0 < s.re) : ‖remainder s‖ ≤ 1 / s.re := by
  rw [mellin_eq]
  have he : -s.re - 1 < -1 := by linarith
  trans ∫ x : ℝ in Ioi 1, x^(-s.re-1)
  · apply norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt he zero_lt_one)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    grw [norm_mul,frac_bound]
    simp [norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx)]
  · simp [integral_Ioi_rpow_of_lt he zero_lt_one]

theorem entireGrowth (hR : 2 ≤ R) (hz : 1/2 ≤ z.re)
    (hn : ‖z‖ ≤ 4*R) : ‖riemannZeta₁ z‖ ≤ R^8 := by
  have hz0 : 0 < z.re := by linarith
  grw [entireFormula hz0, norm_mul, norm_sub_le, norm_mul, norm_sub_le, mellin_bound hz0, ← hz, hn, hn];norm_num
  obtain ⟨u,hu,rfl⟩ := le_iff_exists_nonneg_add.mp hR
  rw [← sub_nonneg]; ring_nf; positivity

abbrev U := ball (0:ℂ) 6⁻¹

abbrev witness (f : ℂ → ℂ) x := ∃ ρ, ‖ρ‖ ≤ 6⁻¹ ∧ f ρ = 0 ∧ x ≤ ((-ρ)⁻¹).re

theorem landau {f : ℂ → ℂ} {B : ℝ}
    (hd : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hb : ∀ w, ‖w‖ ≤ 2⁻¹ → ‖f w‖ ≤ B * ‖f 0‖)
    (hz : ∀ ρ, f ρ = 0 → ρ.re ≤ 0)
    (hx : x = 0 ∨ witness f x) :
    x - (deriv f 0 / f 0).re ≤ 24 * (Real.log B + 1) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B one_lt_two
  induction n generalizing f B x <;> have hB : 1 ≤ B := by nlinarith [hb 0 (by norm_num), norm_pos_iff.mpr h0]
  case zero => simp [hB.not_gt] at hn
  case succ n ih =>
    by_cases has : witness f x
    · obtain ⟨ρ, hr, hzero, hxρ⟩ := has
      let g := dslope f ρ
      have eqf w : f w = (w-ρ)*g w := (sub_smul_dslope_of_zero hzero w).symm
      have hρ : ρ ≠ 0 := by grind
      have hg0 := right_ne_zero_of_mul (eqf 0 ▸ h0)
      have hg : Differentiable ℂ g := differentiableOn_univ.mp ((differentiableOn_dslope univ_mem).mpr hd.differentiableOn)
      have grow w (hw : ‖w‖ ≤ 2⁻¹) : ‖g w‖ ≤ B / 2 * ‖g 0‖ := by
        apply norm_le_of_forall_mem_frontier_norm_le (U:=ball 0 2⁻¹) isBounded_ball hg.diffContOnCl _ (by simpa [closure_ball,mem_closedBall] using hw)
        intro u hu
        simp [frontier_ball] at hu
        have h := hb u hu.le
        simp [eqf u, eqf 0] at h
        nlinarith [norm_sub_norm_le u ρ, norm_nonneg (g u), norm_pos_iff.mpr hρ]
      have ih0 := ih hg hg0 grow
        (fun w _ => hz w (by grind)) (Or.inl rfl) (by rw [pow_succ] at hn; linarith)
      have he := logDeriv_mul 0 (f := (·-ρ)) (by simpa) hg0 (by fun_prop)
        (hg 0)
      simp [←show f = (·-ρ) * g from funext eqf, logDeriv_apply] at he
      simp only [he,add_re,inv_neg] at hxρ ⊢
      -- As in Pi's public #96263, use monotonicity after dividing the growth bound.
      linarith [Real.log_le_log (by positivity) (show B/2≤B by linarith)]
    · obtain rfl := hx.resolve_right has
      have nonzero z (hz' : z ∈ U) : f z ≠ 0 := fun hf => has ⟨z,(mem_ball_zero_iff.mp hz').le,hf,by
        simpa [inv_re] using div_nonpos_of_nonpos_of_nonneg (hz z hf) (normSq_nonneg z)⟩
      have diff := hd.differentiableOn (s:=U)
      grw [zero_sub, neg_le_abs, abs_re_le_norm]
      obtain ⟨g,hgz,hg⟩ := ((diff.deriv isOpen_ball).div diff nonzero).isExactOn_ball.with_val_at 0 0
      have hgd : DifferentiableOn ℂ g U := fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
      let A := Real.log B + 1
      have hm : 0 < A := by dsimp [A]; linarith [Real.log_nonneg hB]
      obtain ⟨c, hc, hfg⟩ := (logDeriv_eqOn_iff diff hgd.cexp isOpen_ball (convex_ball _ _).isPreconnected
        (by simp) nonzero).mp (fun z hz' => by simp [logDeriv_apply,(hg z hz').cexp.deriv])
      have hr z (hz' : z ∈ U) : (g z).re ≤ A := by
        have h := hb z (by linarith [mem_ball_zero_iff.mp hz'])
        simp [hfg hz', hfg (by simp [U] : 0 ∈ U), hgz,norm_exp,mul_comm B,norm_pos_iff.mpr hc] at h
        linarith [(Real.le_log_iff_exp_le (by linarith)).2 h]
      have h := norm_deriv_le_of_forall_mem_sphere_norm_le (R:=12⁻¹) (C:=2*A) (by norm_num)
        (hgd.diffContOnCl_ball (closedBall_subset_ball (by norm_num))) ?_
      · simp [(hg 0 (by simp)).deriv,A] at h ⊢;linarith
      · intro z hz
        have H := borelCaratheodory_zero hm hgd hr (by norm_num) (sphere_subset_ball (by norm_num) hz) hgz
        simp at hz
        norm_num [hz] at H;linarith

lemma good (ha : 1 < z.re) : riemannZeta₁ z ≠ 0 ∧ deriv riemannZeta₁ z / riemannZeta₁ z =
    (z-1)⁻¹ - LSeries (fun n => (Λ n : ℂ)) z := by
  have := riemannZeta_ne_zero_of_one_lt_re ha
  have hn : z ≠ 1 := by grind [one_re]
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div ha]
  grind [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add,riemannZeta_eq_inv_sub_mul]

theorem _root_.AlpogeRHCore1.zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 → 1-c/Real.log (|s.im|+2) ≤ s.re → riemannZeta s ≠ 0 := by
  refine ⟨(2^20)⁻¹,by positivity,fun s hn hs hz => ?_⟩
  let R := |s.im|+2
  have hR : 2 ≤ R := by simp [R]
  have hL := Real.log_two_gt_d9.trans_le (Real.log_le_log (by norm_num) hR)
  have hpos : 0<Real.log R := by linarith
  let d := (2^20:ℝ)⁻¹ / Real.log R
  have hd : 0<d := by positivity
  have tiny : d≤1/100 := (div_le_iff₀ hpos).2 (by linarith)
  change 1-d≤s.re at hs
  have bad : riemannZeta₁ s=0 := by grind [riemannZeta_eq_inv_sub_mul]
  have hht : 1/2≤|s.im| := by
    have hp : 0 < s.re := by linarith
    have eq : (s-1)*remainder s=1 := by grind [entireFormula hp, zero_re]
    have h := mul_le_mul_of_nonneg_left (mellin_bound hp) (norm_nonneg (s-1))
    rw [←norm_mul,eq,norm_one,mul_one_div,le_div_iff₀ hp] at h
    have hb := norm_le_abs_re_add_abs_im (s-1)
    simp at hb
    grind [abs_eq_max_neg]
  let a := s.re+5*d
  have hgap : 4*d≤a-1 := by grind
  have ha : 1<a := by linarith
  have K v := good (z:=⟨a,v⟩) ha
  have W v x (hv:|v|≤2*|s.im|) := landau (f:=fun w => riemannZeta₁ (⟨a,v⟩+w)) (B:=R^8/‖riemannZeta₁ ⟨a,v⟩‖) (x:=x)
    (by fun_prop) (by simpa using (K v).1) (fun w hw => by
      simpa [(K v).1] using entireGrowth hR (z:=⟨a,v⟩+w) (by grind [add_re,abs_re_le_norm w,abs_eq_max_neg]) (by grw [norm_add_le,norm_le_abs_re_add_abs_im (⟨a,v⟩:ℂ)];grind [abs_eq_max_neg,riemannZeta_ne_zero_of_one_le_re]))
    (fun w he => by grind [good (z:=⟨a,v⟩+w),add_re])
  have r := W 0 0 (by simp) (.inl rfl)
  have t := W s.im (5*d)⁻¹ (by linarith) (.inr ⟨(-(5*d):ℝ),by
    simp [abs_of_pos hd];linarith,by convert bad using 2;simp [Complex.ext_iff,a],by simp⟩)
  have u := W (2*s.im) 0 (by simp [abs_mul]) (.inl rfl)
  simp (disch:=first | positivity | simp [(K _).1]) [-inv_re,deriv_comp_const_add,(K _).2,Real.log_div,Real.log_pow] at r t u
  have hp := (1:DirichletCharacter ℂ 1).norm_LFunction_product_ge_one (sub_pos.mpr ha) s.im
  have gap v := (show d≤a-1 by linarith).trans (re_le_norm ((⟨a,v⟩:ℂ)-1))
  simp (disch := grind [one_re]) [DirichletCharacter.LFunctionTrivChar,show ∀ x y:ℂ, x+y=⟨_,_⟩ from fun _ _ => rfl,ofReal_def,riemannZeta_eq_inv_sub_mul] at hp
  repeat grw [←gap] at hp
  apply Real.log_nonneg at hp
  simp [Real.log_mul,Real.log_pow,d,hpos.ne',(good (z:=⟨a,_⟩) ha).1] at hp
  simp [inv_re,normSq_apply] at r
  have pole := inv_anti₀ (by positivity) hgap
  have negt := inv_anti₀ (by norm_num : (0:ℝ)<1/2) hht
  grw [re_le_norm,norm_inv,←abs_im_le_norm ((⟨a,_⟩:ℂ)-1)] at t u <;> try (simp;grind)
  simp [abs_mul,mul_inv_rev] at u
  simp [d,div_eq_mul_inv,mul_inv_rev] at t pole negt
  have S v := hasSum_re (LSeriesSummable_vonMangoldt (s:=⟨a,v⟩) ha).LSeriesHasSum
  have M := HasSum.nonneg (fun n => by
    simp (disch:=simp) [LSeries.term_def₀,cpow_def]
    split_ifs <;> simp_all [exp_re,mul_re,mul_im,log_re,log_im,mul_comm (Real.log _),mul_assoc,Real.cos_two_mul]
    calc
      0 ≤ 2*Λ n*Real.exp _*(1+Real.cos _)^2 := by positivity
      _ = _ := by ring) (((S 0).mul_left 3).add ((S s.im).mul_left 4) |>.add (S (2*s.im)))
  linarith [Real.log_le_self hpos.le,Real.log_two_lt_d9]
end ClassicalZFR
