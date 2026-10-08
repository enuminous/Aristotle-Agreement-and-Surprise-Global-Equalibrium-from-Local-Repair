import RequestProject.Brouwer.DetPoly

/-!
# There is no `C¹` retraction of the closed ball onto its boundary sphere

Let `r` be `C¹` on an open set containing the closed unit ball of `ℝⁿ` (`n ≥ 1`), equal to
the identity on the unit sphere and mapping the open ball into the sphere. For small `t` the
map `r_t = id + t (r - id)` is a diffeomorphism of the open ball onto itself, so the
polynomial `V(t) = ∫_B det D r_t` equals `vol B` for small `t`, hence for all `t`. But
`V(1) = ∫_B det D r = 0` since `r` takes values in the sphere.
-/

open Set Metric Filter Topology MeasureTheory Polynomial

noncomputable section

namespace BrouwerAux

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- A linear map that does not shrink vectors too much has nonzero determinant. -/
theorem det_ne_zero_of_lower_bound {f : 𝔼 →L[ℝ] 𝔼} {c : ℝ} (hc : 0 < c)
    (hf : ∀ v, c * ‖v‖ ≤ ‖f v‖) : f.det ≠ 0 := by
  rw [ContinuousLinearMap.det, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not]
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have := hf v
  simp only [ContinuousLinearMap.coe_coe] at hv
  rw [hv, norm_zero] at this
  have : ‖v‖ = 0 := le_antisymm (by nlinarith [norm_nonneg v]) (norm_nonneg v)
  exact norm_eq_zero.mp this

/-- A linear map with nonzero determinant is surjective. -/
theorem range_eq_top_of_det_ne_zero {f : 𝔼 →L[ℝ] 𝔼} (h : f.det ≠ 0) :
    LinearMap.range (f : 𝔼 →ₗ[ℝ] 𝔼) = ⊤ := by
  rw [ContinuousLinearMap.det, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not] at h
  exact LinearMap.ker_eq_bot_iff_range_eq_top.mp h

/-- `id + A` with `‖A‖ ≤ 1/2` has a lower bound `‖v‖/2`. -/
theorem lower_bound_id_add {A : 𝔼 →L[ℝ] 𝔼} (hA : ‖A‖ ≤ 1 / 2) (v : 𝔼) :
    1 / 2 * ‖v‖ ≤ ‖(ContinuousLinearMap.id ℝ 𝔼 + A) v‖ := by
  have h1 : ‖A v‖ ≤ 1 / 2 * ‖v‖ := (A.le_opNorm v).trans (by gcongr)
  have h2 : ‖v‖ ≤ ‖v + A v‖ + ‖A v‖ := by
    have := norm_sub_le (v + A v) (A v)
    rwa [add_sub_cancel_right] at this
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply]
  linarith

/-- If the derivative of `r` lies in the orthogonal complement of `r x ≠ 0`, `det = 0`. -/
theorem det_eq_zero_of_range_orth {f : 𝔼 →L[ℝ] 𝔼} {w : 𝔼} (hw : w ≠ 0)
    (horth : ∀ v, inner ℝ w (f v) = 0) : f.det = 0 := by
  by_contra h
  have hr := range_eq_top_of_det_ne_zero h
  obtain ⟨v, hv⟩ : w ∈ LinearMap.range (f : 𝔼 →ₗ[ℝ] 𝔼) := by rw [hr]; trivial
  have := horth v
  simp only [ContinuousLinearMap.coe_coe] at hv
  rw [hv, real_inner_self_eq_norm_sq] at this
  exact hw (norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this))

/-- **No `C¹` retraction.** -/
theorem no_C1_retraction {r : 𝔼 → 𝔼} {U : Set 𝔼} (hU : IsOpen U)
    (hBU : closedBall (0 : 𝔼) 1 ⊆ U) (hr : ContDiffOn ℝ 1 r U)
    (hsph : ∀ x : 𝔼, ‖x‖ = 1 → r x = x) (hball : ∀ x ∈ ball (0 : 𝔼) 1, ‖r x‖ = 1) :
    False := by
  -- derivative and its continuity
  set D : 𝔼 → (𝔼 →L[ℝ] 𝔼) := fderiv ℝ r
  have hD : ∀ x ∈ U, HasFDerivAt r (D x) x := fun x hx =>
    ((hr.differentiableOn one_ne_zero) x hx).differentiableAt (hU.mem_nhds hx) |>.hasFDerivAt
  have hDc : ContinuousOn D U := hr.continuousOn_fderiv_of_isOpen hU le_rfl
  set A : 𝔼 → (𝔼 →L[ℝ] 𝔼) := fun x => D x - ContinuousLinearMap.id ℝ 𝔼
  have hAc : ContinuousOn A U := hDc.sub continuousOn_const
  obtain ⟨L, hL⟩ : ∃ L, ∀ x ∈ closedBall (0 : 𝔼) 1, ‖A x‖ ≤ L :=
    (isCompact_closedBall 0 1).exists_bound_of_continuousOn (hAc.mono hBU)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0 (mem_closedBall_self zero_le_one))
  -- the deformation `r_t`
  set rt : ℝ → 𝔼 → 𝔼 := fun t x => x + t • (r x - x)
  have hrt : ∀ t, ∀ x ∈ U, HasFDerivAt (rt t) (ContinuousLinearMap.id ℝ 𝔼 + t • A x) x := by
    intro t x hx
    have := (hasFDerivAt_id x).add (((hD x hx).sub (hasFDerivAt_id x)).const_smul t)
    simpa [rt, A] using this
  -- the integral `V t`
  set V : ℝ → ℝ := fun t => ∫ x in ball (0 : 𝔼) 1, (ContinuousLinearMap.id ℝ 𝔼 + t • A x).det
  have hdetc : ∀ t : ℝ, ContinuousOn (fun x => (ContinuousLinearMap.id ℝ 𝔼 + t • A x).det)
      (closedBall (0 : 𝔼) 1) := fun t =>
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (continuousOn_const.add ((hAc.mono hBU).const_smul t))
  have hint : ∀ t : ℝ, IntegrableOn (fun x => (ContinuousLinearMap.id ℝ 𝔼 + t • A x).det)
      (ball (0 : 𝔼) 1) := fun t =>
    ((hdetc t).integrableOn_compact (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
  -- `V` is a polynomial
  set P : ℝ[X] := ∑ j ∈ nodes 𝔼, C (V j) * lag 𝔼 j
  have hVP : ∀ t, V t = eval t P := by
    intro t
    simp only [V, P, eval_finset_sum, eval_mul, eval_C]
    simp_rw [← integral_mul_const]
    rw [← integral_finset_sum (nodes 𝔼)
      (f := fun (j : ℕ) x => (ContinuousLinearMap.id ℝ 𝔼 + (j : ℝ) • A x).det * eval t (lag 𝔼 j))
      (fun j _ => (hint (j : ℝ)).mul_const _)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact det_add_smul_eq_sum (A x) t
  -- `V 1 = 0`, since `r` maps the ball into the sphere
  have hV1 : V 1 = 0 := by
    have hzero : ∀ x ∈ ball (0 : 𝔼) 1, (ContinuousLinearMap.id ℝ 𝔼 + (1 : ℝ) • A x).det = 0 := by
      intro x hx
      have hxU : x ∈ U := hBU (ball_subset_closedBall hx)
      have hDx : ContinuousLinearMap.id ℝ 𝔼 + (1 : ℝ) • A x = D x := by simp [A]
      rw [hDx]
      have hrx : r x ≠ 0 := by
        intro h; have := hball x hx; rw [h, norm_zero] at this; norm_num at this
      refine det_eq_zero_of_range_orth hrx fun v => ?_
      -- differentiate `s ↦ ‖r (x + s v)‖² = 1` at `s = 0`
      have hline : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
      have hc : HasDerivAt (fun s : ℝ => r (x + s • v)) (D x v) 0 := by
        exact (hD x hxU).comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
      have hφ := HasDerivAt.inner ℝ hc hc
      have hev : (fun s : ℝ => inner ℝ (r (x + s • v)) (r (x + s • v))) =ᶠ[𝓝 0]
          fun _ => (1 : ℝ) := by
        have hcont : ContinuousAt (fun s : ℝ => x + s • v) 0 := hline.continuousAt
        have : ∀ᶠ s in 𝓝 (0 : ℝ), x + s • v ∈ ball (0 : 𝔼) 1 :=
          hcont.preimage_mem_nhds (by simpa using isOpen_ball.mem_nhds hx)
        filter_upwards [this] with s hs
        rw [real_inner_self_eq_norm_sq, hball _ hs]; norm_num
      have h0 := (hφ.congr_of_eventuallyEq hev.symm).unique (hasDerivAt_const (0 : ℝ) (1 : ℝ))
      simp only [zero_smul, add_zero] at h0
      have := real_inner_comm (D x v) (r x)
      linarith
    simp only [V]
    rw [setIntegral_congr_fun measurableSet_ball hzero, integral_zero]
  -- for small `t`, `V t = vol B`
  set c : ℝ := (volume (ball (0 : 𝔼) 1)).toReal
  set t₀ : ℝ := min (1 / 2) (1 / (2 * (L + 1)))
  have ht₀ : 0 < t₀ := lt_min (by norm_num) (by positivity)
  have hVsmall : ∀ t ∈ Ioo 0 t₀, V t = c := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have ht_half : t ≤ 1 / 2 := ht1.le.trans (min_le_left _ _)
    have htL : t * L ≤ 1 / 2 := by
      have h := ht1.le.trans (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at h
      nlinarith
    have hsA : ∀ s ∈ Icc 0 t, ∀ x ∈ closedBall (0 : 𝔼) 1, ‖s • A x‖ ≤ 1 / 2 := by
      intro s hs x hx
      rw [norm_smul, Real.norm_of_nonneg hs.1]
      calc s * ‖A x‖ ≤ t * L := mul_le_mul hs.2 (hL x hx) (norm_nonneg _) ht0.le
        _ ≤ 1 / 2 := htL
    -- positivity of the Jacobian
    have hpos : ∀ x ∈ closedBall (0 : 𝔼) 1, 0 < (ContinuousLinearMap.id ℝ 𝔼 + t • A x).det := by
      intro x hx
      by_contra hneg
      push_neg at hneg
      have hcont : ContinuousOn (fun s : ℝ => (ContinuousLinearMap.id ℝ 𝔼 + s • A x).det)
          (Icc 0 t) :=
        (ContinuousLinearMap.continuous_det.comp
          (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht0.le hcont
        (show (0 : ℝ) ∈ Icc _ _ from ⟨hneg, by simp [ContinuousLinearMap.det]⟩)
      exact det_ne_zero_of_lower_bound (by norm_num : (0 : ℝ) < 1 / 2)
        (lower_bound_id_add (hsA s hs x hx)) hs0
    -- `r - id` is `L`-Lipschitz on the closed ball
    have hlip : ∀ x ∈ closedBall (0 : 𝔼) 1, ∀ y ∈ closedBall (0 : 𝔼) 1,
        ‖(r y - y) - (r x - x)‖ ≤ L * ‖y - x‖ := by
      intro x hx y hy
      refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fun z => r z - z)
        (f' := A) ?_ hL (convex_closedBall 0 1) hx hy
      intro z hz
      exact ((hD z (hBU hz)).sub (hasFDerivAt_id z)).hasFDerivWithinAt
    -- injectivity
    have hinj : InjOn (rt t) (ball (0 : 𝔼) 1) := by
      intro x hx y hy hxy
      have h := hlip x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)
      have e : y - x = -(t • ((r y - y) - (r x - x))) := by
        have : y - x + t • ((r y - y) - (r x - x)) = rt t y - rt t x := by
          simp only [rt]; module
        rw [hxy, sub_self] at this
        exact eq_neg_of_add_eq_zero_left this
      have hn : ‖y - x‖ ≤ 1 / 2 * ‖y - x‖ := by
        calc ‖y - x‖ = t * ‖(r y - y) - (r x - x)‖ := by
              rw [e, norm_neg, norm_smul, Real.norm_of_nonneg ht0.le]
          _ ≤ t * (L * ‖y - x‖) := by gcongr
          _ = (t * L) * ‖y - x‖ := by ring
          _ ≤ 1 / 2 * ‖y - x‖ := by gcongr
      have : ‖y - x‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (y - x)]) (norm_nonneg _)
      exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm
    -- `r_t` maps the ball into itself
    have hmaps : MapsTo (rt t) (ball (0 : 𝔼) 1) (ball (0 : 𝔼) 1) := by
      intro x hx
      have hx' := mem_ball_zero_iff.mp hx
      rw [mem_ball_zero_iff]
      have e : rt t x = (1 - t) • x + t • r x := by simp only [rt]; module
      rw [e]
      calc ‖(1 - t) • x + t • r x‖ ≤ ‖(1 - t) • x‖ + ‖t • r x‖ := norm_add_le _ _
        _ = (1 - t) * ‖x‖ + t * ‖r x‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
            Real.norm_of_nonneg ht0.le]
        _ < 1 := by rw [hball x hx]; nlinarith
    -- the image of the ball is open (inverse function theorem)
    have hopen : IsOpen (rt t '' ball (0 : 𝔼) 1) := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨x, hx, rfl⟩
      have hxU := hBU (ball_subset_closedBall hx)
      have hcd : ContDiffAt ℝ 1 (rt t) x :=
        contDiffAt_id.add (((hr.contDiffAt (hU.mem_nhds hxU)).sub contDiffAt_id).const_smul t)
      have hstrict := hcd.hasStrictFDerivAt' (hrt t x hxU) one_ne_zero
      have hsurj := range_eq_top_of_det_ne_zero (hpos x (ball_subset_closedBall hx)).ne'
      rw [← hstrict.map_nhds_eq_of_surj hsurj]
      exact image_mem_map (isOpen_ball.mem_nhds hx)
    -- the image of the ball is relatively closed in the ball
    have hcontrt : ContinuousOn (rt t) (closedBall (0 : 𝔼) 1) := fun x hx =>
      (hrt t x (hBU hx)).continuousAt.continuousWithinAt
    have hclosure : closure (rt t '' ball (0 : 𝔼) 1) ∩ ball (0 : 𝔼) 1 ⊆
        rt t '' ball (0 : 𝔼) 1 := by
      rintro y ⟨hy, hyb⟩
      have hcomp : IsCompact (rt t '' closedBall (0 : 𝔼) 1) :=
        (isCompact_closedBall 0 1).image_of_continuousOn hcontrt
      have hy' : y ∈ rt t '' closedBall (0 : 𝔼) 1 :=
        (hcomp.isClosed.closure_subset_iff.mpr (image_mono ball_subset_closedBall)) hy
      obtain ⟨x, hx, rfl⟩ := hy'
      by_cases hxb : ‖x‖ < 1
      · exact ⟨x, mem_ball_zero_iff.mpr hxb, rfl⟩
      · exfalso
        have hx1 : ‖x‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp hx) (not_lt.mp hxb)
        have : rt t x = x := by simp [rt, hsph x hx1]
        rw [this, mem_ball_zero_iff, hx1] at hyb
        exact lt_irrefl _ hyb
    have himage : rt t '' ball (0 : 𝔼) 1 = ball (0 : 𝔼) 1 := by
      refine Subset.antisymm hmaps.image_subset ?_
      exact (convex_ball (0 : 𝔼) 1).isPreconnected.subset_of_closure_inter_subset hopen
        ⟨rt t 0, hmaps (mem_ball_self one_pos), ⟨0, mem_ball_self one_pos, rfl⟩⟩ hclosure
    -- change of variables
    have hcov := lintegral_abs_det_fderiv_eq_addHaar_image volume measurableSet_ball
      (fun x hx => (hrt t x (hBU (ball_subset_closedBall hx))).hasFDerivWithinAt) hinj
    rw [himage] at hcov
    simp only [V, c]
    rw [integral_eq_lintegral_of_nonneg_ae]
    · congr 1
      rw [← hcov]
      refine setLIntegral_congr_fun measurableSet_ball fun x hx => ?_
      simp only
      rw [abs_of_pos (hpos x (ball_subset_closedBall hx))]
    · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact (hpos x (ball_subset_closedBall hx)).le
    · exact (hint t).aestronglyMeasurable
  -- hence `V ≡ c`, contradicting `V 1 = 0`
  have hPc : P - C c = 0 := by
    refine eq_zero_of_infinite_isRoot _ ((Ioo_infinite ht₀).mono fun t ht => ?_)
    simp only [mem_setOf_eq, IsRoot, eval_sub, eval_C, ← hVP, hVsmall t ht, sub_self]
  have : V 1 = c := by
    rw [hVP, sub_eq_zero.mp hPc, eval_C]
  have hcpos : 0 < c := by
    have h1 : volume (ball (0 : 𝔼) 1) ≠ ⊤ := measure_ball_lt_top.ne
    have h2 : volume (ball (0 : 𝔼) 1) ≠ 0 := (measure_ball_pos volume 0 one_pos).ne'
    exact ENNReal.toReal_pos h2 h1
  linarith

end BrouwerAux
