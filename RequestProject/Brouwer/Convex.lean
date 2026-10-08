import RequestProject.Brouwer.Ball

/-!
# Brouwer's fixed-point theorem for compact convex sets

Every continuous self-map of a nonempty compact convex subset of a finite-dimensional real
normed space has a fixed point. We reduce to the closed unit ball of `ℝⁿ` by a linear
isomorphism, the nearest-point projection onto the convex set, and a rescaling.
-/

open Set Metric

noncomputable section

namespace BrouwerAux

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- The nearest-point projection onto a nonempty complete convex set: existence and the
variational characterisation. -/
theorem exists_proj {K : Set 𝔼} (hKne : K.Nonempty) (hKc : IsComplete K) (hKv : Convex ℝ K)
    (u : 𝔼) : ∃ v ∈ K, ∀ w ∈ K, inner ℝ (u - v) (w - v) ≤ 0 := by
  obtain ⟨v, hv, heq⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKc hKv u
  exact ⟨v, hv, (norm_eq_iInf_iff_real_inner_le_zero hKv hv).mp heq⟩

/-- The nearest-point projection onto `K` is a continuous retraction onto `K`. -/
theorem exists_retraction_convex {K : Set 𝔼} (hKne : K.Nonempty) (hKc : IsComplete K)
    (hKv : Convex ℝ K) :
    ∃ P : 𝔼 → 𝔼, Continuous P ∧ (∀ u, P u ∈ K) ∧ ∀ u ∈ K, P u = u := by
  choose P hPK hPvar using exists_proj hKne hKc hKv
  refine ⟨P, ?_, hPK, ?_⟩
  · -- `P` is `1`-Lipschitz
    refine (LipschitzWith.of_dist_le_mul fun u₁ u₂ => ?_).continuous (K := 1)
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    have h1 := hPvar u₁ (P u₂) (hPK u₂)
    have h2 := hPvar u₂ (P u₁) (hPK u₁)
    have key : ‖P u₁ - P u₂‖ ^ 2 ≤ inner ℝ (u₁ - u₂) (P u₁ - P u₂) := by
      have e1 : inner ℝ (u₁ - P u₁) (P u₂ - P u₁) + inner ℝ (u₂ - P u₂) (P u₁ - P u₂) =
          inner ℝ (u₁ - u₂) (P u₂ - P u₁) + ‖P u₁ - P u₂‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_sub_left, inner_sub_right, real_inner_comm]
        ring
      have e2 : inner ℝ (u₁ - u₂) (P u₂ - P u₁) = -inner ℝ (u₁ - u₂) (P u₁ - P u₂) := by
        rw [← inner_neg_right, neg_sub]
      linarith
    have hcs := real_inner_le_norm (u₁ - u₂) (P u₁ - P u₂)
    by_cases h0 : ‖P u₁ - P u₂‖ = 0
    · rw [h0]; exact norm_nonneg _
    · have hpos : 0 < ‖P u₁ - P u₂‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
  · intro u hu
    have h := hPvar u u hu
    have : inner ℝ (u - P u) (u - P u) ≤ 0 := h
    rw [real_inner_self_eq_norm_sq] at this
    have : ‖u - P u‖ = 0 := by nlinarith [norm_nonneg (u - P u)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm

/-- Brouwer's theorem for nonempty compact convex subsets of `ℝⁿ`. -/
theorem brouwer_euclidean {K : Set 𝔼} (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hKne : K.Nonempty) {f : 𝔼 → 𝔼} (hf : ContinuousOn f K) (hfK : MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  obtain ⟨P, hPc, hPK, hPid⟩ := exists_retraction_convex hKne hKc.isComplete hKv
  obtain ⟨R₀, hR₀⟩ := hKc.isBounded.subset_closedBall (0 : 𝔼)
  set R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : K ⊆ closedBall (0 : 𝔼) R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  set F : 𝔼 → 𝔼 := fun y => R⁻¹ • f (P (R • y))
  have hFc : Continuous F :=
    continuous_const.smul (hf.comp_continuous (hPc.comp (continuous_const.smul continuous_id))
      fun y => hPK _)
  have hFB : MapsTo F (closedBall 0 1) (closedBall 0 1) := by
    intro y _
    rw [mem_closedBall_zero_iff]
    have : ‖f (P (R • y))‖ ≤ R := mem_closedBall_zero_iff.mp (hKR (hfK (hPK _)))
    simp only [F, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR]
    rw [inv_mul_le_iff₀ hR, mul_one]
    exact this
  obtain ⟨y, -, hy⟩ := brouwer_closedBall hFc.continuousOn hFB
  -- `x = R y` is a fixed point
  have hxeq : f (P (R • y)) = R • y := by
    have := congrArg (fun z => R • z) hy
    simp only [F, smul_smul, mul_inv_cancel₀ hR.ne', one_smul] at this
    exact this
  have hxK : R • y ∈ K := hxeq ▸ hfK (hPK _)
  refine ⟨R • y, hxK, ?_⟩
  rw [← hPid _ hxK]
  rw [hPid _ hxK] at hxeq ⊢
  exact hxeq

end BrouwerAux

/-- **Brouwer's fixed-point theorem.** Every continuous self-map of a nonempty compact convex
subset of a finite-dimensional real normed space has a fixed point. -/
theorem brouwer_fixed_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hKne : K.Nonempty) {f : E → E} (hf : ContinuousOn f K) (hfK : MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  set e := toEuclidean (E := E)
  set K' := e '' K
  set f' := fun y => e (f (e.symm y))
  have hK'c : IsCompact K' := hKc.image e.continuous
  have hK'v : Convex ℝ K' := hKv.linear_image (e.toLinearEquiv.toLinearMap)
  have hK'ne : K'.Nonempty := hKne.image _
  have hesymm : MapsTo e.symm K' K := by
    rintro _ ⟨x, hx, rfl⟩; simpa using hx
  have hf' : ContinuousOn f' K' :=
    e.continuous.comp_continuousOn (hf.comp e.symm.continuous.continuousOn hesymm)
  have hf'K : MapsTo f' K' K' := fun y hy => ⟨_, hfK (hesymm hy), rfl⟩
  obtain ⟨y, hy, hfy⟩ := BrouwerAux.brouwer_euclidean hK'c hK'v hK'ne hf' hf'K
  refine ⟨e.symm y, hesymm hy, ?_⟩
  have := congrArg e.symm hfy
  simpa [f'] using this
