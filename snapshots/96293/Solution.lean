import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.LogDeriv

/- The entire completion of (s−1)ζ(s) allows all three logarithmic derivatives
   to be estimated with the same disk lemma, including the real center. -/
open Complex Metric Set Filter MeasureTheory Asymptotics Topology ArithmeticFunction
noncomputable section
namespace ClassicalZFR
variable {s z : ℂ} {x : ℝ}
abbrev frac : ℝ → ℂ := ofReal ∘ Int.fract
abbrev tail := (Ioi 1).indicator frac

lemma frac_bound x : ‖frac x‖ ≤ 1 := by
  simpa [frac,Int.abs_fract] using (Int.fract_lt_one x).le
abbrev remainder (z:ℂ) := ∫ x in Ioi (1:ℝ), (x:ℂ)^(-z-1)*frac x
lemma tail_smooth (hs : s.re<0) : DifferentiableAt ℂ (mellin tail) s := by
  have hb x : ‖tail x‖ ≤ 1 := (norm_indicator_le_norm_self frac x).trans (frac_bound x)
  apply mellin_differentiableAt_of_isBigO_rpow (a:=0) (b:=s.re-1)
  · exact (locallyIntegrableOn_const (1:ℂ)).mono (by measurability) (by simpa using Eventually.of_forall hb)
  · exact isBigO_of_le _ fun x => by simpa using hb x
  · exact hs
  · apply IsBigO.of_bound'
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with x (hx:x<1)
    simp [tail,mem_Ioi,hx.not_gt]
  · linarith

lemma remainder_eq : remainder = fun z => mellin tail (-z) := by
  funext z; rw [mellin,tail,←indicator_smul,setIntegral_indicator measurableSet_Ioi];simp [remainder]

lemma entireFormula (hs : 0 < s.re) : riemannZeta₁ s = s * (1-(s-1)*remainder s) := by
  apply (differentiable_riemannZeta₁.differentiableOn.analyticOnNhd (isOpen_re_gt 0)).eqOn_of_preconnected_of_eventuallyEq
    (DifferentiableOn.analyticOnNhd (by intro z hz; have := tail_smooth (s:=-z) (by simpa using hz); rw [remainder_eq]; fun_prop) (isOpen_re_gt 0))
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by norm_num) _ hs
  filter_upwards [(isOpen_re_gt 1).mem_nhds (by norm_num : 1 < (2:ℂ).re)] with z hz
  have h := LSeries_eq_mul_integral' (1 : ℕ → ℂ) zero_le_one hz (by simp; rfl)
  simp [LSeries_one_eq_riemannZeta hz] at h
  have hi := integral_Ioi_cpow_of_lt (a := -z) (by simpa) zero_lt_one
  simp [← neg_sub z 1,neg_add_eq_sub,-neg_sub] at hi
  suffices riemannZeta z = z*(z-1)⁻¹ - z * remainder z by
    have hn : z ≠ 1 := by grind [one_re]
    grind [riemannZeta_eq_inv_sub_mul hn]
  rw [h, ← hi, remainder, ← mul_sub, ← integral_sub
    (integrableOn_Ioi_cpow_of_lt (by simpa) zero_lt_one)
    ((integrableOn_Ioi_cpow_of_lt (by simp;linarith) zero_lt_one).mul_bdd
      (by fun_prop : Measurable frac).aestronglyMeasurable (.of_forall frac_bound))]
  congr 1; refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hxC := ofReal_ne_zero.mpr hx0.ne'
  simp [frac, Int.fract, ← Int.natCast_floor_eq_floor hx0.le,
    neg_add_eq_sub,cpow_neg, cpow_sub _ _ hxC]; field [hxC]

lemma mellin_bound (hs : 0 < s.re) : ‖remainder s‖ ≤ 1 / s.re := by
  have he : -s.re - 1 < -1 := by linarith
  refine (norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt he zero_lt_one) ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    grw [norm_mul,frac_bound]
    simp [norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx)]
  · simp [integral_Ioi_rpow_of_lt he zero_lt_one]

lemma growth (h : 1/2≤z.re) : ‖riemannZeta₁ z‖≤(2*‖z‖+2)^2 := by
  have hp : 0<z.re := by linarith
  grw [entireFormula hp,norm_mul,norm_sub_le,norm_mul,norm_sub_le,mellin_bound hp,←h];norm_num
  nlinarith [norm_nonneg z]

abbrev U := ball (0:ℂ) 6⁻¹

abbrev witness (f : ℂ → ℂ) x := ∃ ρ, ‖ρ‖ ≤ 6⁻¹ ∧ f ρ = 0 ∧ x ≤ -(ρ⁻¹).re

theorem landau {f : ℂ → ℂ} {B : ℝ}
    (hd : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hb : ∀ w, ‖w‖ ≤ 2⁻¹ → ‖f w‖ ≤ B * ‖f 0‖)
    (hz : ∀ ρ, f ρ = 0 → ρ.re ≤ 0)
    (hx : x = 0 ∨ witness f x) :
    x - (logDeriv f 0).re ≤ 24 * (Real.log B + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2*B)
  induction n generalizing f B x <;> have hB := one_le_of_le_mul_right₀ (norm_pos_iff.mpr h0) (hb 0 (by simp))
  case zero => grind
  case succ n ih =>
    by_cases has : witness f x
    · obtain ⟨ρ, hr, hzero, hxρ⟩ := has
      obtain ⟨g,hg,rfl⟩ : ∃ g, Differentiable ℂ g ∧ (·-ρ)*g=f :=
        ⟨_,differentiableOn_univ.mp ((differentiableOn_dslope univ_mem).mpr hd.differentiableOn),
        funext (sub_smul_dslope_of_zero hzero)⟩
      simp at h0 hz
      have ih0 := ih (B:=B/2) hg h0.2 (fun w hw => by
        apply norm_le_of_forall_mem_frontier_norm_le (U:=ball 0 2⁻¹) isBounded_ball hg.diffContOnCl _ (by simpa [closure_ball] using hw)
        intro u hu
        simp [frontier_ball] at hu hb
        nlinarith [hb u hu.le,norm_sub_norm_le u ρ, norm_nonneg (g u), norm_pos_iff.mpr h0.1])
        (by grind) (.inl rfl) (by grind)
      rw [logDeriv_mul] <;> first | fun_prop | simp_all [logDeriv_apply (·-ρ),-inv_re]
      -- As in Pi's public #96263, use monotonicity after dividing the growth bound.
      linarith [Real.log_le_log (by positivity) (half_le_self (zero_le_one.trans hB))]
    · obtain rfl := hx.resolve_right has
      have nonzero z (hz' : z ∈ U) hf := has ⟨z,(mem_ball_zero_iff.mp hz').le,hf,by
        simpa [inv_re] using div_nonpos_of_nonpos_of_nonneg (hz z hf) (normSq_nonneg z)⟩
      have diff := hd.differentiableOn (s:=U)
      grw [zero_sub, neg_le_abs, abs_re_le_norm]
      obtain ⟨g,hgz,hg⟩ := ((diff.deriv isOpen_ball).div diff nonzero).isExactOn_ball.with_val_at 0 0
      have hgd : DifferentiableOn ℂ g U := fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
      let A := Real.log B + 1
      have hm : 0 < A := add_pos_of_nonneg_of_pos (Real.log_nonneg hB) zero_lt_one
      obtain ⟨c, hc, hfg⟩ := (logDeriv_eqOn_iff diff hgd.cexp isOpen_ball isPreconnected_ball
        (by simp) nonzero).mp (fun z hz' => by simp [logDeriv_apply,(hg z hz').cexp.deriv])
      have hr z (hz' : z ∈ U) : (g z).re ≤ A := by
        have h := hb z (by linarith [mem_ball_zero_iff.mp hz'])
        simp [hfg hz', hfg (by simp : 0 ∈ U), hgz,norm_exp,mul_comm B,norm_pos_iff.mpr hc] at h
        linarith [(Real.le_log_iff_exp_le (by linarith)).2 h]
      have h := norm_deriv_le_of_forall_mem_sphere_norm_le (R:=12⁻¹) (C:=2*A) (by norm_num)
        (hgd.diffContOnCl_ball (closedBall_subset_ball (by norm_num))) ?_
      · simp [(hg 0 (by simp)).deriv,A,logDeriv_apply] at h ⊢;linarith
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
  have hL := Real.log_two_gt_d9.trans_le (Real.log_le_log zero_lt_two hR)
  have hpos : 0<Real.log R := by linarith
  let d := (2^20:ℝ)⁻¹ / Real.log R
  have hd : 0<d := by positivity
  have tiny : d≤1/100 := (div_le_iff₀ hpos).2 (by linarith)
  change 1-d≤s.re at hs
  have bad : riemannZeta₁ s=0 := by grind [riemannZeta_eq_inv_sub_mul]
  have hht : 1/2≤|s.im| := by
    have hp : 0 < s.re := by linarith
    have eq : remainder s = (s-1)⁻¹ := by grind [entireFormula hp, zero_re]
    have h := mellin_bound hp
    simp [eq,one_div,inv_le_inv₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hn)) hp] at h
    have hb := norm_le_abs_re_add_abs_im (s-1)
    simp at hb
    grind [abs_eq_max_neg]
  let a := s.re+5*d
  have hgap : 2^2*d≤a-1 := by grind
  have ha : 1<a := by linarith
  have K v := good (z:=⟨a,v⟩) ha
  have W v x (hv:|v|≤2*|s.im|) := landau (f:=fun w => riemannZeta₁ (⟨a,v⟩+w)) (B:=(2^4*R)^2/‖riemannZeta₁ ⟨a,v⟩‖) (x:=x)
    (by fun_prop) (by simpa using (K v).1) (fun w hw => by
      simp [(K v).1]
      grw [growth (by grind [add_re,abs_re_le_norm w,abs_eq_max_neg]),norm_add_le,norm_le_abs_re_add_abs_im (⟨a,v⟩:ℂ)]
      gcongr
      grind [abs_eq_max_neg,riemannZeta_ne_zero_of_one_le_re])
    (fun w he => by grind [good (z:=⟨a,v⟩+w),add_re])
  have r := W 0 0 (by simp) (.inl rfl)
  have t := W s.im (5*d)⁻¹ (by linarith) (.inr ⟨(-(5*d):ℝ),by
    simp [abs_of_pos hd];linarith,by convert bad using 2;simp [Complex.ext_iff,a],by simp⟩)
  have u := W (2*s.im) 0 (by simp [abs_mul]) (.inl rfl)
  have hp := (1:DirichletCharacter ℂ 1).norm_LFunction_product_ge_one (sub_pos.mpr ha) s.im
  have gap v := hgap.trans (re_le_norm ((⟨a,v⟩:ℂ)-1))
  simp (disch := grind [one_re]) [DirichletCharacter.LFunctionTrivChar,show ∀ x y:ℂ, x+y=⟨_,_⟩ from fun _ _ => rfl,ofReal_def,riemannZeta_eq_inv_sub_mul] at hp
  repeat grw [←gap] at hp
  apply Real.log_nonneg at hp
  simp (disch:=first | positivity | simp [hpos.ne',(K _).1]) [-inv_re,logDeriv_apply,deriv_comp_const_add,(K _).2,Real.log_div,Real.log_mul,Real.log_pow,d] at hp r t u
  simp [inv_re,normSq_apply] at r
  have pole := inv_anti₀ (by positivity) hgap
  have negt := inv_anti₀ (by norm_num) hht
  grw [re_le_norm,norm_inv,←abs_im_le_norm ((⟨a,_⟩:ℂ)-1)] at t u <;> try (simp;grind)
  simp [d,abs_mul,div_eq_mul_inv,mul_inv_rev] at t u pole negt
  -- The trigonometric square supplies positivity at all three heights.
  have S v := hasSum_re (LSeriesSummable_vonMangoldt (s:=⟨a,v⟩) ha).LSeriesHasSum
  have M := HasSum.nonneg (fun n => by
    simp [LSeries.term_def₀,cpow_def]
    split_ifs <;> simp_all [exp_re,mul_re,mul_im,log_re,log_im,mul_comm (Real.log _),mul_assoc,Real.cos_two_mul]
    calc
      0 ≤ 2*Λ n*Real.exp _*(1+Real.cos _)^2 := by positivity
      _ = _ := by ring) (((S 0).mul_left 3).add ((S s.im).mul_left 4) |>.add (S (2*s.im)))
  linarith [Real.log_le_self hpos.le,Real.log_two_lt_d9]
end ClassicalZFR
