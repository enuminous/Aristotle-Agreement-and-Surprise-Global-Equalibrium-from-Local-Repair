import RequestProject.Defs

/-!
# Averages agree where states do not (Section 3.4)

Proposition 8, the damped discrete identity, Corollaries 9 and 10, the Lipschitz closure-gap
bound, and Proposition 11 (charge balance).
-/

open Set Filter Topology MeasureTheory intervalIntegral

noncomputable section

namespace Repair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Time average `(1/T) ∫₀ᵀ f(t) dt`. -/
def timeAvg (f : ℝ → E) (T : ℝ) : E := T⁻¹ • ∫ t in (0 : ℝ)..T, f t

/-- The integrated relaxation equation: `x(T) - x(0) = T (R̄_T - x̄_T)`. -/
theorem relaxation_integral_identity {R : E → E} {X : Set E} (hRc : ContinuousOn R X)
    {x : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hx : ∀ t ∈ Icc 0 T, HasDerivAt x (R (x t) - x t) t) (hxX : ∀ t ∈ Icc 0 T, x t ∈ X) :
    x T - x 0 = T • (timeAvg (fun t => R (x t)) T - timeAvg x T) := by
  have hxc : ContinuousOn x (Icc 0 T) := fun t ht => (hx t ht).continuousAt.continuousWithinAt
  have hRxc : ContinuousOn (fun t => R (x t)) (Icc 0 T) := hRc.comp hxc (fun t ht => hxX t ht)
  have hi1 : IntervalIntegrable (fun t => R (x t)) volume 0 T :=
    (hRxc.mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
  have hi2 : IntervalIntegrable x volume 0 T :=
    (hxc.mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
  have hftc : ∫ t in (0 : ℝ)..T, (R (x t) - x t) = x T - x 0 :=
    integral_eq_sub_of_hasDerivAt (fun t ht => hx t (by rwa [uIcc_of_le hT.le] at ht))
      (hi1.sub hi2)
  rw [← hftc, integral_sub hi1 hi2, timeAvg, timeAvg, ← smul_sub, smul_smul,
    mul_inv_cancel₀ hT.ne', one_smul]

/-- **Proposition 8 (Agreement on average).** Along a relaxation trajectory `ẋ = R(x) - x`
in a bounded set `X`, `‖x̄_T - R̄_T‖ ≤ diam X / T`. -/
theorem agreement_on_average {R : E → E} {X : Set E} (hXb : Bornology.IsBounded X)
    (hRc : ContinuousOn R X) {x : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hx : ∀ t ∈ Icc 0 T, HasDerivAt x (R (x t) - x t) t) (hxX : ∀ t ∈ Icc 0 T, x t ∈ X) :
    ‖timeAvg x T - timeAvg (fun t => R (x t)) T‖ ≤ Metric.diam X / T := by
  have h := relaxation_integral_identity hRc hT hx hxX
  have hd : ‖x T - x 0‖ ≤ Metric.diam X := by
    rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem hXb (hxX T ⟨hT.le, le_rfl⟩) (hxX 0 ⟨le_rfl, hT.le⟩)
  rw [h, norm_smul, Real.norm_of_nonneg hT.le, norm_sub_rev] at hd
  rw [le_div_iff₀ hT]
  linarith

omit [CompleteSpace E] in
/-- **Damped discrete identity.** `(1/N) ∑_{k<N} (R(x_k) - x_k) = (x_N - x_0)/(η N)`. -/
theorem damped_average_identity (R : E → E) {η : ℝ} (hη : η ≠ 0) (x₀ : E) (N : ℕ) :
    ∑ k ∈ Finset.range N, (R (damped R η x₀ k) - damped R η x₀ k) =
      η⁻¹ • (damped R η x₀ N - x₀) := by
  induction N with
  | zero => simp [damped]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [damped, dampedStep]
    rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hη, one_smul]
    abel

omit [CompleteSpace E] in
/-- **Damped discrete bound.** If the damped sequence stays in a bounded set `X`, then
`‖(1/N) ∑_{k<N} (R(x_k) - x_k)‖ ≤ diam X / (η N)`. -/
theorem damped_average_bound {R : E → E} {X : Set E} (hXb : Bornology.IsBounded X)
    {η : ℝ} (hη : 0 < η) {x₀ : E} (hX : ∀ k, damped R η x₀ k ∈ X) {N : ℕ} (hN : 0 < N) :
    ‖(N : ℝ)⁻¹ • ∑ k ∈ Finset.range N, (R (damped R η x₀ k) - damped R η x₀ k)‖ ≤
      Metric.diam X / (η * N) := by
  rw [damped_average_identity R hη.ne', smul_smul, norm_smul, ← dist_eq_norm]
  have hd := Metric.dist_le_diam_of_mem hXb (hX N) (hX 0)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show damped R η x₀ 0 = x₀ from rfl] at hd
  rw [Real.norm_of_nonneg (by positivity), div_eq_mul_inv, mul_inv]
  calc (↑N)⁻¹ * η⁻¹ * dist (damped R η x₀ N) x₀ ≤ (↑N)⁻¹ * η⁻¹ * Metric.diam X := by gcongr
    _ = Metric.diam X * (η⁻¹ * (↑N)⁻¹) := by ring

/-- The time average of a trajectory staying in a closed convex set stays in it. -/
theorem timeAvg_mem {X : Set E} (hXc : IsClosed X) (hXv : Convex ℝ X) {x : ℝ → E} {T : ℝ}
    (hT : 0 < T) (hxc : ContinuousOn x (Icc 0 T)) (hxX : ∀ t ∈ Icc 0 T, x t ∈ X) :
    timeAvg x T ∈ X := by
  have : timeAvg x T = ⨍ t in Ioc 0 T, x t := by
    rw [timeAvg, setAverage_eq, Real.volume_real_Ioc_of_le hT.le, integral_of_le hT.le, sub_zero]
  rw [this]
  refine hXv.set_average_mem hXc (by simp [hT]) (by simp) ?_ ?_
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun t ht => hxX t (Ioc_subset_Icc_self ht)
  · exact hxc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- **Corollary 9 (Linear repair).** If `X` is bounded, closed and convex and `R` is affine,
`R x = A x + c`, then every limit point of the time averages `x̄_T` (as `T → ∞`) of a
relaxation trajectory in `X` is an equilibrium in `X`. -/
theorem linear_repair_limit_points {X : Set E} (hXb : Bornology.IsBounded X)
    (hXc : IsClosed X) (hXv : Convex ℝ X) (A : E →L[ℝ] E) (c : E) {x : ℝ → E}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (A (x t) + c - x t) t) (hxX : ∀ t, 0 ≤ t → x t ∈ X)
    {p : E} (hp : MapClusterPt p atTop (timeAvg x)) : p ∈ X ∧ A p + c = p := by
  set R : E → E := fun y => A y + c
  have hRc : Continuous R := A.continuous.add continuous_const
  -- the average of `R ∘ x` is `R` of the average
  have havg : ∀ T, 0 < T → timeAvg (fun t => R (x t)) T = R (timeAvg x T) := by
    intro T hT
    have hxc : ContinuousOn x (Icc 0 T) := fun t ht =>
      (hx t ht.1).continuousAt.continuousWithinAt
    have hi : IntervalIntegrable x volume 0 T :=
      (hxc.mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
    simp only [timeAvg, R]
    have hAi : IntervalIntegrable (fun t => A (x t)) volume 0 T :=
      ((A.continuous.comp_continuousOn hxc).mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
    rw [intervalIntegral.integral_add hAi _root_.intervalIntegrable_const,
      A.intervalIntegral_comp_comm hi, intervalIntegral.integral_const, smul_add, map_smul,
      smul_smul, sub_zero, inv_mul_cancel₀ hT.ne', one_smul]
  have hmem : ∀ᶠ T in atTop, timeAvg x T ∈ X := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    exact timeAvg_mem hXc hXv hT (fun t ht => (hx t ht.1).continuousAt.continuousWithinAt)
      (fun t ht => hxX t ht.1)
  have hpX : p ∈ X := hXc.closure_eq ▸ clusterPt_iff_forall_mem_closure.mp hp X hmem
  refine ⟨hpX, ?_⟩
  -- `g y = y - R y` tends to `0` along the averages
  set g : E → E := fun y => y - R y
  have hgc : Continuous g := continuous_id.sub hRc
  have hlim : Tendsto (fun T => g (timeAvg x T)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hdiv : Tendsto (fun T : ℝ => Metric.diam X / T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hdiv
    filter_upwards [eventually_gt_atTop 0] with T hT
    have h := agreement_on_average hXb hRc.continuousOn hT (R := R)
      (fun t ht => hx t ht.1) (fun t ht => hxX t ht.1)
    rw [havg T hT] at h
    exact h
  have hcl : MapClusterPt (g p) atTop (fun T => g (timeAvg x T)) :=
    hp.tendsto_comp (hgc.tendsto p)
  have : g p = 0 := eq_of_nhds_neBot (ClusterPt.mono hcl hlim)
  exact (sub_eq_zero.mp this).symm

/-- **Lipschitz closure gap.** For a repair map that is `L`-Lipschitz on a bounded closed
convex `X`, along a relaxation trajectory in `X`,
`‖R(x̄_T) - x̄_T‖ ≤ diam X / T + (L / T) ∫₀ᵀ ‖x(t) - x̄_T‖ dt`. -/
theorem lipschitz_closure_gap {R : E → E} {X : Set E} {L : ℝ} (hXb : Bornology.IsBounded X)
    (hXc : IsClosed X) (hXv : Convex ℝ X) (hL : ∀ y ∈ X, ∀ z ∈ X, ‖R y - R z‖ ≤ L * ‖y - z‖)
    {x : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hx : ∀ t ∈ Icc 0 T, HasDerivAt x (R (x t) - x t) t) (hxX : ∀ t ∈ Icc 0 T, x t ∈ X) :
    ‖R (timeAvg x T) - timeAvg x T‖ ≤
      Metric.diam X / T + L / T * ∫ t in (0 : ℝ)..T, ‖x t - timeAvg x T‖ := by
  have hRc : ContinuousOn R X := by
    have : LipschitzOnWith ⟨max L 0, le_max_right _ _⟩ R X :=
      LipschitzOnWith.of_dist_le_mul fun y hy z hz => by
        rw [dist_eq_norm, dist_eq_norm]
        refine (hL y hy z hz).trans ?_
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    exact this.continuousOn
  have hxc : ContinuousOn x (Icc 0 T) := fun t ht => (hx t ht).continuousAt.continuousWithinAt
  have hRxc : ContinuousOn (fun t => R (x t)) (Icc 0 T) := hRc.comp hxc (fun t ht => hxX t ht)
  set xb := timeAvg x T
  have hxb : xb ∈ X := timeAvg_mem hXc hXv hT hxc hxX
  have h8 := agreement_on_average hXb hRc hT hx hxX
  have hi1 : IntervalIntegrable (fun t => R (x t)) volume 0 T :=
    (hRxc.mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
  -- `R(x̄) - R̄ = T⁻¹ ∫ (R x̄ - R (x t))`
  have hdiff : R xb - timeAvg (fun t => R (x t)) T =
      T⁻¹ • ∫ t in (0 : ℝ)..T, (R xb - R (x t)) := by
    rw [intervalIntegral.integral_sub _root_.intervalIntegrable_const hi1,
      intervalIntegral.integral_const, sub_zero, smul_sub, smul_smul,
      inv_mul_cancel₀ hT.ne', one_smul, timeAvg]
  have hint : ‖∫ t in (0 : ℝ)..T, (R xb - R (x t))‖ ≤
      ∫ t in (0 : ℝ)..T, L * ‖x t - xb‖ := by
    refine intervalIntegral.norm_integral_le_of_norm_le hT.le ?_ ?_
    · refine Eventually.of_forall fun t ht => ?_
      have := hL xb hxb (x t) (hxX t (Ioc_subset_Icc_self ht))
      rwa [norm_sub_rev xb] at this
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hT.le]
      exact continuousOn_const.mul ((hxc.sub continuousOn_const).norm)
  rw [intervalIntegral.integral_const_mul] at hint
  have hsplit : R xb - xb = (timeAvg (fun t => R (x t)) T - xb) +
      (R xb - timeAvg (fun t => R (x t)) T) := by abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_sub_rev] at h8
  rw [hdiff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hT.le)]
  have : T⁻¹ * ‖∫ t in (0 : ℝ)..T, (R xb - R (x t))‖ ≤
      L / T * ∫ t in (0 : ℝ)..T, ‖x t - xb‖ := by
    rw [div_eq_inv_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hT.le)
  linarith

end Repair

namespace RateLaw

open Repair

variable {V : Type*} [Fintype V]

/-- **Corollary 10 (Rate law).** Let each node integrate a weighted sum of signals emitted
by its neighbours, `Rᵢ(x) = ∑ⱼ Wᵢⱼ sⱼ(xⱼ) + eᵢ`, with continuous signals `sⱼ`, and let `x`
be a relaxation trajectory with `|xᵢ(t)| ≤ M`. Then the average potentials and the average
signals satisfy `|x̄ᵢ - (∑ⱼ Wᵢⱼ s̄ⱼ + eᵢ)| ≤ 2M / T`, i.e.
`x̄ᵢ = ∑ⱼ Wᵢⱼ s̄ⱼ + eᵢ + O(1/T)`. -/
theorem rate_law (W : V → V → ℝ) (s : V → ℝ → ℝ) (hs : ∀ j, Continuous (s j)) (e : V → ℝ)
    {x : ℝ → V → ℝ} {T M : ℝ} (hT : 0 < T)
    (hx : ∀ i, ∀ t ∈ Icc 0 T,
      HasDerivAt (fun t => x t i) (∑ j, W i j * s j (x t j) + e i - x t i) t)
    (hM : ∀ i, ∀ t ∈ Icc 0 T, |x t i| ≤ M) (i : V) :
    |timeAvg (fun t => x t i) T -
        (∑ j, W i j * timeAvg (fun t => s j (x t j)) T + e i)| ≤ 2 * M / T := by
  have hxc : ∀ j, ContinuousOn (fun t => x t j) (Icc 0 T) := fun j t ht =>
    (hx j t ht).continuousAt.continuousWithinAt
  have hxi : ∀ j, IntervalIntegrable (fun t => x t j) volume 0 T := fun j =>
    ((hxc j).mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
  have hsi : ∀ j, IntervalIntegrable (fun t => s j (x t j)) volume 0 T := fun j =>
    (((hs j).comp_continuousOn (hxc j)).mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
  have hsum : IntervalIntegrable (fun t => ∑ j, W i j * s j (x t j)) volume 0 T :=
    by
      convert IntervalIntegrable.sum Finset.univ (fun j _ => (hsi j).const_mul (W i j)) using 1
      funext t; simp [Finset.sum_apply]
  have hftc := integral_eq_sub_of_hasDerivAt (fun t ht => hx i t (by rwa [uIcc_of_le hT.le] at ht))
    ((hsum.add _root_.intervalIntegrable_const).sub (hxi i))
  rw [intervalIntegral.integral_sub (hsum.add _root_.intervalIntegrable_const) (hxi i),
    intervalIntegral.integral_add hsum _root_.intervalIntegrable_const,
    intervalIntegral.integral_finset_sum (fun j _ => (hsi j).const_mul _),
    intervalIntegral.integral_const] at hftc
  simp only [intervalIntegral.integral_const_mul, sub_zero, smul_eq_mul] at hftc
  simp only [timeAvg, smul_eq_mul]
  have key : (T⁻¹ * ∫ t in (0 : ℝ)..T, x t i) -
      (∑ j, W i j * (T⁻¹ * ∫ t in (0 : ℝ)..T, s j (x t j)) + e i) =
      -(T⁻¹ * (x T i - x 0 i)) := by
    have hs' : ∑ j, W i j * (T⁻¹ * ∫ t in (0 : ℝ)..T, s j (x t j)) =
        T⁻¹ * ∑ j, W i j * ∫ t in (0 : ℝ)..T, s j (x t j) := by
      rw [Finset.mul_sum]; congr 1; funext j; ring
    rw [hs', ← hftc]
    field_simp
    ring
  rw [key, abs_neg, abs_mul, abs_of_pos (inv_pos.mpr hT), inv_mul_eq_div]
  gcongr
  have h1 := hM i T ⟨hT.le, le_rfl⟩
  have h2 := hM i 0 ⟨le_rfl, hT.le⟩
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith

end RateLaw

namespace ChargeBalance

variable {V : Type*} [Fintype V]

/-- **Proposition 11 (Charge balance).** Integrated (distributional) form of the spiking
equations of node `i` on the window `[0, T]`:

* current: `τ ġᵢ = -gᵢ + τ ∑ⱼ wᵢⱼ ∑ₖ δ(t - tⱼᵏ)` integrates to
  `τ (gᵢ(T) - gᵢ(0)) = -∫₀ᵀ gᵢ + τ ∑ⱼ wᵢⱼ nⱼ`, where `nⱼ` is the number of spikes of node `j`
  in the window;
* potential: `τₘ u̇ᵢ = -uᵢ + gᵢ`, with each of the `nᵢ` spikes of node `i` resetting `uᵢ`
  from the threshold `ϑ` to `0`, integrates to
  `τₘ (uᵢ(T) - uᵢ(0)) = ∫₀ᵀ (gᵢ - uᵢ) - τₘ ϑ nᵢ`.

If potentials and currents are bounded by `M`, the firing rates `νⱼ = nⱼ / T` and the
average potential `ūᵢ` satisfy `τₘ ϑ νᵢ = τ ∑ⱼ wᵢⱼ νⱼ - ūᵢ` up to an explicit `O(1/T)` error. -/
theorem charge_balance (w : V → ℝ) (n : V → ℕ) (i : V) {τm τ ϑ T M : ℝ} {u g : ℝ → ℝ}
    (hτm : 0 < τm) (hτ : 0 < τ) (hT : 0 < T)
    (hg : τ * (g T - g 0) = -(∫ t in (0 : ℝ)..T, g t) + τ * ∑ j, w j * n j)
    (hu : τm * (u T - u 0) = (∫ t in (0 : ℝ)..T, g t) - (∫ t in (0 : ℝ)..T, u t) - τm * ϑ * n i)
    (hgM : |g T| ≤ M ∧ |g 0| ≤ M) (huM : |u T| ≤ M ∧ |u 0| ≤ M) :
    |τm * ϑ * (n i / T) - (τ * ∑ j, w j * (n j / T) - (∫ t in (0 : ℝ)..T, u t) / T)| ≤
      2 * (τ + τm) * M / T := by
  have key : τm * ϑ * (n i / T) - (τ * ∑ j, w j * (n j / T) - (∫ t in (0 : ℝ)..T, u t) / T) =
      -(τ * (g T - g 0) + τm * (u T - u 0)) / T := by
    have : ∑ j, w j * ((n j : ℝ) / T) = (∑ j, w j * n j) / T := by
      rw [Finset.sum_div]; congr 1; funext j; ring
    rw [this]
    field_simp
    linarith
  rw [key, abs_div, abs_of_pos hT]
  gcongr
  rw [abs_neg]
  obtain ⟨h1, h2⟩ := hgM
  obtain ⟨h3, h4⟩ := huM
  rw [abs_le] at h1 h2 h3 h4 ⊢
  constructor <;> nlinarith

end ChargeBalance
