import RequestProject.Brouwer.NoRetraction

/-!
# Brouwer's fixed-point theorem for the closed unit ball of `ℝⁿ`

From a fixed-point-free continuous self-map of the closed ball we build a smooth
fixed-point-free self-map (by smoothing), and from it a `C¹` retraction onto the sphere
(following the ray from `g x` through `x`), contradicting `no_C1_retraction`.
-/

open Set Metric Filter Topology

noncomputable section

namespace BrouwerAux

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- **Retraction from a fixed-point-free `C¹` self-map of the ball.** -/
theorem exists_retraction {g : 𝔼 → 𝔼} (hg : ContDiff ℝ 1 g)
    (hgB : MapsTo g (closedBall 0 1) (closedBall 0 1))
    (hfix : ∀ x ∈ closedBall (0 : 𝔼) 1, g x ≠ x) :
    ∃ (r : 𝔼 → 𝔼) (U : Set 𝔼), IsOpen U ∧ closedBall (0 : 𝔼) 1 ⊆ U ∧ ContDiffOn ℝ 1 r U ∧
      (∀ x : 𝔼, ‖x‖ = 1 → r x = x) ∧ (∀ x ∈ ball (0 : 𝔼) 1, ‖r x‖ = 1) := by
  set u : 𝔼 → 𝔼 := fun x => x - g x
  set a : 𝔼 → ℝ := fun x => inner ℝ x (u x)
  set b : 𝔼 → ℝ := fun x => inner ℝ (u x) (u x)
  set c : 𝔼 → ℝ := fun x => 1 - inner ℝ x x
  set d : 𝔼 → ℝ := fun x => a x ^ 2 + b x * c x
  set lam : 𝔼 → ℝ := fun x => (-a x + Real.sqrt (d x)) / b x
  set r : 𝔼 → 𝔼 := fun x => x + lam x • u x
  set U : Set 𝔼 := {x | 0 < b x ∧ 0 < d x}
  have hu : ContDiff ℝ 1 u := contDiff_id.sub hg
  have ha : ContDiff ℝ 1 a := contDiff_id.inner ℝ hu
  have hb : ContDiff ℝ 1 b := hu.inner ℝ hu
  have hc : ContDiff ℝ 1 c := contDiff_const.sub (contDiff_id.inner ℝ contDiff_id)
  have hd : ContDiff ℝ 1 d := (ha.pow 2).add (hb.mul hc)
  have hbx : ∀ x, b x = ‖u x‖ ^ 2 := fun x => real_inner_self_eq_norm_sq _
  have hcx : ∀ x, c x = 1 - ‖x‖ ^ 2 := fun x => by simp [c]
  -- on the sphere, `a > 0`
  have ha_pos : ∀ x : 𝔼, ‖x‖ = 1 → 0 < a x := by
    intro x hx
    have hxB : x ∈ closedBall (0 : 𝔼) 1 := mem_closedBall_zero_iff.mpr hx.le
    have hgx : ‖g x‖ ≤ 1 := mem_closedBall_zero_iff.mp (hgB hxB)
    have hax : a x = 1 - inner ℝ x (g x) := by
      simp only [a, u, inner_sub_right, real_inner_self_eq_norm_sq, hx]; norm_num
    have hcs : inner ℝ x (g x) ≤ 1 := by
      have := real_inner_le_norm x (g x)
      rw [hx] at this; linarith
    rcases hcs.lt_or_eq with h | h
    · linarith
    · exfalso
      apply hfix x hxB
      have : ‖x - g x‖ ^ 2 = 0 := by
        have e := norm_sub_sq_real x (g x)
        rw [hx, h] at e
        nlinarith [norm_nonneg (g x)]
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm
  refine ⟨r, U, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isOpen_lt continuous_const hb.continuous).inter
      (isOpen_lt continuous_const hd.continuous)
  · intro x hx
    have hxn := mem_closedBall_zero_iff.mp hx
    have hb0 : 0 < b x := by
      rw [hbx]
      have : u x ≠ 0 := fun h => hfix x hx (sub_eq_zero.mp h).symm
      positivity
    refine ⟨hb0, ?_⟩
    rcases hxn.lt_or_eq with h | h
    · have : 0 < c x := by rw [hcx]; nlinarith [norm_nonneg x]
      have : 0 < b x * c x := mul_pos hb0 this
      simp only [d]; nlinarith [sq_nonneg (a x)]
    · have : c x = 0 := by rw [hcx, h]; norm_num
      simp only [d, this, mul_zero, add_zero]
      exact pow_pos (ha_pos x h) 2
  · intro x hx
    obtain ⟨hb0, hd0⟩ := hx
    have hlam : ContDiffAt ℝ 1 lam x :=
      ((ha.contDiffAt.neg).add (hd.contDiffAt.sqrt hd0.ne')).div hb.contDiffAt hb0.ne'
    exact (contDiffAt_id.add (hlam.smul hu.contDiffAt)).contDiffWithinAt
  · intro x hx
    have hc0 : c x = 0 := by rw [hcx, hx]; norm_num
    have hd' : d x = a x ^ 2 := by simp only [d, hc0, mul_zero, add_zero]
    have : lam x = 0 := by
      simp only [lam, hd', Real.sqrt_sq (ha_pos x hx).le, neg_add_cancel, zero_div]
    simp [r, this]
  · intro x hx
    have hxB := ball_subset_closedBall hx
    have hxn := mem_ball_zero_iff.mp hx
    have hb0 : 0 < b x := by
      rw [hbx]
      have : u x ≠ 0 := fun h => hfix x hxB (sub_eq_zero.mp h).symm
      positivity
    have hc0 : 0 < c x := by rw [hcx]; nlinarith [norm_nonneg x]
    have hd0 : 0 ≤ d x := by simp only [d]; nlinarith [sq_nonneg (a x), mul_pos hb0 hc0]
    have hs := Real.sq_sqrt hd0
    have hsq : ‖r x‖ ^ 2 = 1 := by
      have e : ‖r x‖ ^ 2 = ‖x‖ ^ 2 + 2 * lam x * a x + lam x ^ 2 * b x := by
        simp only [r]
        rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
          ← hbx]
        ring
      rw [e]
      have hcx' := hcx x
      have hlam : lam x * b x = -a x + Real.sqrt (d x) := by
        simp only [lam]; field_simp
      have : 2 * lam x * a x + lam x ^ 2 * b x = c x := by
        have h1 : (2 * lam x * a x + lam x ^ 2 * b x) * b x =
            2 * a x * (lam x * b x) + (lam x * b x) ^ 2 := by ring
        rw [hlam] at h1
        have h2 : (2 * lam x * a x + lam x ^ 2 * b x) * b x = c x * b x := by
          rw [h1]; simp only [d] at hs; nlinarith [hs]
        exact mul_right_cancel₀ hb0.ne' h2
      linarith [this, hcx']
    have := pow_eq_one_iff_of_nonneg (norm_nonneg (r x)) (by norm_num : 2 ≠ 0) |>.mp hsq
    exact this

/-- Smooth approximation on the closed ball of a continuous function. -/
theorem exists_smooth_approx {F : 𝔼 → 𝔼} (hF : Continuous F) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h : 𝔼 → 𝔼, ContDiff ℝ 1 h ∧ ∀ x ∈ closedBall (0 : 𝔼) 1, dist (h x) (F x) ≤ δ := by
  have huc : UniformContinuousOn F (closedBall (0 : 𝔼) 2) :=
    (isCompact_closedBall 0 2).uniformContinuousOn_of_continuous hF.continuousOn
  obtain ⟨ε', hε', hε'F⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ
  set ε := min ε' 1
  have hε : 0 < ε := lt_min hε' one_pos
  obtain ⟨h, hh, hdist⟩ := hF.exists_contDiff_dist_le_of_forall_mem_ball_dist_le hε
  refine ⟨h, hh.of_le (by norm_num), fun x hx => hdist x δ fun y hy => ?_⟩
  have hx1 := mem_closedBall_zero_iff.mp hx
  have hyx : dist y x < ε := hy
  have hy2 : y ∈ closedBall (0 : 𝔼) 2 := by
    rw [mem_closedBall_zero_iff]
    have := norm_le_norm_add_norm_sub' y x
    rw [← dist_eq_norm] at this
    linarith [min_le_right ε' 1]
  have hx2 : x ∈ closedBall (0 : 𝔼) 2 := by
    rw [mem_closedBall_zero_iff]; linarith
  exact (hε'F y hy2 x hx2 (hyx.trans_le (min_le_left _ _))).le

/-- **Brouwer's fixed-point theorem for the closed unit ball of `ℝⁿ`.** -/
theorem brouwer_closedBall {f : 𝔼 → 𝔼} (hf : ContinuousOn f (closedBall 0 1))
    (hfB : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : 𝔼) 1, f x = x := by
  by_contra hcon
  push_neg at hcon
  -- the minimal displacement `δ`
  have hcomp := isCompact_closedBall (0 : 𝔼) 1
  obtain ⟨x₀, hx₀, hmin⟩ := hcomp.exists_isMinOn ⟨0, mem_closedBall_self zero_le_one⟩
    ((continuousOn_id.sub hf).norm)
  set δ := ‖x₀ - f x₀‖
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr (hcon x₀ hx₀).symm)
  have hδx : ∀ x ∈ closedBall (0 : 𝔼) 1, δ ≤ ‖x - f x‖ := fun x hx => hmin hx
  -- extend `f` continuously by radial projection
  set P : 𝔼 → 𝔼 := fun x => (max 1 ‖x‖)⁻¹ • x
  have hPc : Continuous P :=
    ((continuous_const.max continuous_norm).inv₀ fun x =>
      (lt_of_lt_of_le one_pos (le_max_left _ _)).ne').smul continuous_id
  have hPB : ∀ x, P x ∈ closedBall (0 : 𝔼) 1 := by
    intro x
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos (lt_of_lt_of_le one_pos (le_max_left _ _))]
    rw [inv_mul_le_iff₀ (lt_of_lt_of_le one_pos (le_max_left _ _)), mul_one]
    exact le_max_right _ _
  have hPid : ∀ x ∈ closedBall (0 : 𝔼) 1, P x = x := by
    intro x hx
    simp [P, max_eq_left (mem_closedBall_zero_iff.mp hx)]
  set F : 𝔼 → 𝔼 := fun x => f (P x)
  have hFc : Continuous F := hf.comp_continuous hPc hPB
  -- smooth approximation, rescaled into the ball
  set ε := δ / 3
  have hε : 0 < ε := by positivity
  obtain ⟨h, hh, hhF⟩ := exists_smooth_approx hFc hε
  set g : 𝔼 → 𝔼 := fun x => (1 + ε)⁻¹ • h x
  have hg : ContDiff ℝ 1 g := hh.const_smul _
  have hfx : ∀ x ∈ closedBall (0 : 𝔼) 1, dist (h x) (f x) ≤ ε := by
    intro x hx
    have := hhF x hx
    simp only [F, hPid x hx] at this
    exact this
  have hgB : MapsTo g (closedBall 0 1) (closedBall 0 1) := by
    intro x hx
    rw [mem_closedBall_zero_iff]
    have h1 : ‖h x‖ ≤ 1 + ε := by
      have := norm_le_norm_add_norm_sub' (h x) (f x)
      rw [← dist_eq_norm] at this
      have := mem_closedBall_zero_iff.mp (hfB hx)
      linarith [hfx x hx]
    simp only [g, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + ε)]
    rw [inv_mul_le_iff₀ (by linarith), mul_one]
    exact h1
  have hgfix : ∀ x ∈ closedBall (0 : 𝔼) 1, g x ≠ x := by
    intro x hx heq
    have hfn := mem_closedBall_zero_iff.mp (hfB hx)
    have hgf : ‖g x - f x‖ ≤ 2 * ε := by
      have e : g x - f x = (1 + ε)⁻¹ • (h x - f x) - (ε / (1 + ε)) • f x := by
        simp only [g]
        rw [smul_sub, sub_sub, ← add_smul]
        congr 1
        rw [show (1 + ε)⁻¹ + ε / (1 + ε) = 1 by field_simp, one_smul]
      rw [e]
      calc ‖(1 + ε)⁻¹ • (h x - f x) - (ε / (1 + ε)) • f x‖
          ≤ ‖(1 + ε)⁻¹ • (h x - f x)‖ + ‖(ε / (1 + ε)) • f x‖ := norm_sub_le _ _
        _ = (1 + ε)⁻¹ * ‖h x - f x‖ + ε / (1 + ε) * ‖f x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (by positivity), abs_of_pos (by positivity)]
        _ ≤ 2 * ε := by
          have h1 : (1 + ε)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
          have h2 : ε / (1 + ε) ≤ ε := div_le_self hε.le (by linarith)
          have h3 : ‖h x - f x‖ ≤ ε := by rw [← dist_eq_norm]; exact hfx x hx
          have h4 := mul_le_mul h1 h3 (norm_nonneg _) zero_le_one
          have h5 := mul_le_mul h2 hfn (norm_nonneg _) hε.le
          linarith
    have := hδx x hx
    rw [heq] at hgf
    have hεδ : ε = δ / 3 := rfl
    linarith
  obtain ⟨r, U, hU, hBU, hr, hsph, hball⟩ := exists_retraction hg hgB hgfix
  exact no_C1_retraction hU hBU hr hsph hball

end BrouwerAux
