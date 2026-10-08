import Mathlib

/-!
# Existence without reachability (Proposition 7)

Two nodes holding numbers in `[-1, 1]` with repair maps
`R₁(x₁, x₂) = clip(2x₁ - 2x₂)`, `R₂(x₁, x₂) = clip(2x₁ + 2x₂)`.
-/

open Set Filter Topology

noncomputable section

namespace TwoNodeLoop

/-- Truncation to `[-1, 1]`. -/
def clip (t : ℝ) : ℝ := max (-1) (min 1 t)

/-- The repair map of the two-node loop. -/
def R (p : ℝ × ℝ) : ℝ × ℝ := (clip (2 * p.1 - 2 * p.2), clip (2 * p.1 + 2 * p.2))

/-- The square `[-1, 1]²`. -/
def square : Set (ℝ × ℝ) := Icc (-1) 1 ×ˢ Icc (-1) 1

theorem clip_mem (t : ℝ) : clip t ∈ Icc (-1 : ℝ) 1 := by
  unfold clip; constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem clip_of_abs_le {t : ℝ} (h : |t| ≤ 1) : clip t = t := by
  rw [abs_le] at h
  unfold clip
  rw [min_eq_right h.2, max_eq_right h.1]

theorem clip_sq_le (t : ℝ) : clip t ^ 2 ≤ t ^ 2 := by
  unfold clip
  rcases le_total t 1 with h1 | h1 <;> rcases le_total (-1) t with h2 | h2
  · rw [min_eq_right h1, max_eq_right h2]
  · rw [min_eq_right h1, max_eq_left (by linarith)]; nlinarith
  · rw [min_eq_left h1, max_eq_right (by norm_num)]; nlinarith
  · linarith

theorem clip_eq_zero {t : ℝ} : clip t = 0 ↔ t = 0 := by
  unfold clip
  constructor
  · intro h
    rcases le_total t 1 with h1 | h1
    · rw [min_eq_right h1] at h
      rcases le_total (-1) t with h2 | h2
      · rwa [max_eq_right h2] at h
      · rw [max_eq_left h2] at h; norm_num at h
    · rw [min_eq_left h1, max_eq_right (by norm_num)] at h; norm_num at h
  · rintro rfl; norm_num

theorem continuous_clip : Continuous clip :=
  continuous_const.max (continuous_const.min continuous_id)

theorem continuous_R : Continuous R :=
  (continuous_clip.comp (by fun_prop)).prodMk (continuous_clip.comp (by fun_prop))

/-- The network satisfies the hypotheses of the existence theorem (Theorem 4): the square is
nonempty, compact and convex, and `R` is continuous and maps it into itself. -/
theorem hypotheses_existence :
    square.Nonempty ∧ IsCompact square ∧ Convex ℝ square ∧ Continuous R ∧ MapsTo R square square :=
  ⟨⟨(0, 0), ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩, isCompact_Icc.prod isCompact_Icc,
    (convex_Icc _ _).prod (convex_Icc _ _), continuous_R,
    fun p _ => ⟨clip_mem _, clip_mem _⟩⟩

theorem clip_cases {t s : ℝ} (h : clip t = s) :
    (t ≤ -1 ∧ s = -1) ∨ (-1 ≤ t ∧ t ≤ 1 ∧ s = t) ∨ (1 ≤ t ∧ s = 1) := by
  unfold clip at h
  rcases le_total t 1 with h1 | h1
  · rw [min_eq_right h1] at h
    rcases le_total (-1) t with h2 | h2
    · rw [max_eq_right h2] at h; exact Or.inr (Or.inl ⟨h2, h1, h.symm⟩)
    · rw [max_eq_left h2] at h; exact Or.inl ⟨h2, h.symm⟩
  · rw [min_eq_left h1, max_eq_right (by norm_num)] at h; exact Or.inr (Or.inr ⟨h1, h.symm⟩)

/-- **Proposition 7 (uniqueness of the equilibrium).** The only fixed point of `R`
(in the square, or indeed in the whole plane) is `(0, 0)`. -/
theorem fixed_iff (p : ℝ × ℝ) : R p = p ↔ p = 0 := by
  constructor
  · intro h
    obtain ⟨a, b⟩ := p
    simp only [R, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rcases clip_cases h1 with ⟨c1, d1⟩ | ⟨c1, c1', d1⟩ | ⟨c1, d1⟩ <;>
    rcases clip_cases h2 with ⟨c2, d2⟩ | ⟨c2, c2', d2⟩ | ⟨c2, d2⟩ <;>
    first
    | (exfalso; linarith)
    | (ext <;> simp <;> linarith)
  · rintro rfl; simp [R, clip]

/-- `R` vanishes only at the origin. -/
theorem R_eq_zero {p : ℝ × ℝ} (h : R p = 0) : p = 0 := by
  obtain ⟨a, b⟩ := p
  simp only [R, Prod.mk_eq_zero, clip_eq_zero] at h
  ext <;> simp <;> linarith [h.1, h.2]

/-- Squared Euclidean norm. -/
def sq (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2

theorem sq_pos_of_ne {p : ℝ × ℝ} (h : p ≠ 0) : 0 < sq p := by
  obtain ⟨a, b⟩ := p
  unfold sq
  by_contra hc
  apply h
  have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  simp [ha, hb]

/-- In the disc `sq p < 1/16` no clipping happens. -/
theorem R_linear {p : ℝ × ℝ} (h : sq p < 1 / 16) :
    R p = (2 * p.1 - 2 * p.2, 2 * p.1 + 2 * p.2) := by
  obtain ⟨a, b⟩ := p
  unfold sq at h
  simp only at h
  have ha : |a| < 1 / 4 := by
    rw [← abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    exact sq_lt_sq.mp (by nlinarith [sq_nonneg b])
  have hb : |b| < 1 / 4 := by
    rw [← abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    exact sq_lt_sq.mp (by nlinarith [sq_nonneg a])
  rw [abs_lt] at ha hb
  simp only [R]
  rw [clip_of_abs_le (by rw [abs_le]; constructor <;> linarith),
    clip_of_abs_le (by rw [abs_le]; constructor <;> linarith)]

theorem sq_tendsto_zero {x : ℕ → ℝ × ℝ} (h : Tendsto x atTop (𝓝 0)) :
    Tendsto (fun t => sq (x t)) atTop (𝓝 0) := by
  have hc : Continuous sq := by unfold sq; fun_prop
  simpa [sq] using (hc.tendsto 0).comp h

/-- **Proposition 7 (synchronous repair).** From any start other than `(0, 0)`, synchronous
repair `x_{t+1} = R(x_t)` does not converge. -/
theorem synchronous_not_tendsto {x₀ : ℝ × ℝ} (h0 : x₀ ≠ 0) (p : ℝ × ℝ) :
    ¬ Tendsto (fun t : ℕ => R^[t] x₀) atTop (𝓝 p) := by
  intro hlim
  set x : ℕ → ℝ × ℝ := fun t => R^[t] x₀
  -- the limit is a fixed point, hence the origin
  have hsucc : Tendsto (fun t => x (t + 1)) atTop (𝓝 (R p)) := by
    have := (continuous_R.tendsto p).comp hlim
    refine this.congr fun t => ?_
    simp [x, Function.iterate_succ_apply']
  have hp : R p = p := tendsto_nhds_unique hsucc ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  rw [fixed_iff] at hp
  subst hp
  have hne : ∀ t, x t ≠ 0 := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih =>
      intro hz
      apply ih
      apply R_eq_zero
      simpa [x, Function.iterate_succ_apply'] using hz
  have hsq := sq_tendsto_zero hlim
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp (hsq.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/16)))
  -- beyond `t₀` the squared norm is multiplied by 8 at each step, so it does not decrease
  have hmono : ∀ k, sq (x t₀) ≤ sq (x (t₀ + k)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hlt := ht₀ (t₀ + k) (by omega)
      have hstep : x (t₀ + (k + 1)) = R (x (t₀ + k)) := by
        simp [x, ← add_assoc, Function.iterate_succ_apply']
      rw [hstep, R_linear hlt]
      unfold sq at ih ⊢
      simp only
      nlinarith [sq_nonneg (x (t₀ + k)).1, sq_nonneg (x (t₀ + k)).2]
  have hpos := sq_pos_of_ne (hne t₀)
  have : ∀ᶠ t in atTop, sq (x t₀) / 2 < sq (x t) := by
    filter_upwards [eventually_ge_atTop t₀] with t ht
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    linarith [hmono k]
  have hlim0 := hsq.eventually (gt_mem_nhds (by linarith : (0:ℝ) < sq (x t₀) / 2))
  obtain ⟨t, h1, h2⟩ := (this.and hlim0).exists
  linarith

/-- If a trajectory of `ẋ = F(x)` with continuous `F` converges, its limit is a zero of `F`. -/
theorem limit_is_rest {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → E}
    (hF : Continuous F) {x : ℝ → E} (hx : ∀ t, 0 ≤ t → HasDerivAt x (F (x t)) t) {p : E}
    (hlim : Tendsto x atTop (𝓝 p)) : F p = 0 := by
  by_contra hv
  set v := F p
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  -- eventually `F (x t)` is within `‖v‖/2` of `v`
  have hev : ∀ᶠ t in atTop, ‖F (x t) - v‖ < ‖v‖ / 2 := by
    have := ((hF.tendsto p).comp hlim)
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    exact this.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ t in atTop, ‖x t - p‖ < ‖v‖ / 8 := by
    rw [tendsto_iff_norm_sub_tendsto_zero] at hlim
    exact hlim.eventually (gt_mem_nhds (by linarith))
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp (hev.and (hev2.and (eventually_ge_atTop 0)))
  -- `y t = x t - t • v` moves slowly beyond `t₀`
  set y : ℝ → E := fun t => x t - t • v
  have hy : ∀ t, t₀ ≤ t → HasDerivAt y (F (x t) - v) t := by
    intro t ht
    have := (hx t ((ht₀ t₀ le_rfl).2.2.trans ht)).sub ((hasDerivAt_id t).smul_const v)
    simpa [y] using this
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment' (f := y) (a := t₀) (b := t₀ + 1)
    (f' := fun t => F (x t) - v) (C := ‖v‖ / 2)
    (fun t ht => (hy t ht.1).hasDerivWithinAt) (fun t ht => (ht₀ t ht.1).1.le) (t₀ + 1)
    ⟨by linarith, le_rfl⟩
  have h1 := (ht₀ (t₀ + 1) (by linarith)).2.1
  have h2 := (ht₀ t₀ le_rfl).2.1
  -- `x (t₀+1) - x t₀ = v + (y (t₀+1) - y t₀)`
  have hxy : x (t₀ + 1) - x t₀ = v + (y (t₀ + 1) - y t₀) := by
    simp only [y, add_smul, one_smul]; abel
  have : ‖v‖ ≤ ‖x (t₀ + 1) - x t₀‖ + ‖y (t₀ + 1) - y t₀‖ := by
    have hv' : v = (x (t₀ + 1) - x t₀) - (y (t₀ + 1) - y t₀) := by rw [hxy]; abel
    rw [hv']
    exact norm_sub_le _ _
  have h3 : ‖x (t₀ + 1) - x t₀‖ ≤ ‖x (t₀ + 1) - p‖ + ‖x t₀ - p‖ := by
    have := norm_sub_le (x (t₀ + 1) - p) (x t₀ - p)
    rwa [sub_sub_sub_cancel_right] at this
  simp only [add_sub_cancel_left, mul_one] at hbound
  linarith

/-- **Proposition 7 (relaxation).** No relaxation trajectory `ẋ = R(x) - x` that starts away
from `(0, 0)` converges. -/
theorem relaxation_not_tendsto {x : ℝ → ℝ × ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (R (x t) - x t) t) (h0 : x 0 ≠ 0) (p : ℝ × ℝ) :
    ¬ Tendsto x atTop (𝓝 p) := by
  intro hlim
  have hp : R p - p = 0 :=
    limit_is_rest (continuous_R.sub continuous_id) hx hlim
  rw [sub_eq_zero, fixed_iff] at hp
  subst hp
  -- `g t = ‖x t‖²` and its derivative
  set g : ℝ → ℝ := fun t => sq (x t)
  have hg : ∀ t, 0 ≤ t → HasDerivAt g
      (2 * (x t).1 * ((R (x t)).1 - (x t).1) + 2 * (x t).2 * ((R (x t)).2 - (x t).2)) t := by
    intro t ht
    have h := hx t ht
    have h1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h
    have h2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h
    have := (h1.pow 2).add (h2.pow 2)
    convert this using 1
    simp [Function.comp]
  -- Step A: `g` never vanishes, since `g' ≥ -11 g`
  have hgpos : ∀ t, 0 ≤ t → 0 < g t := by
    set k : ℝ → ℝ := fun t => g t * Real.exp (11 * t)
    have hk : ∀ t, 0 ≤ t → HasDerivAt k
        ((2 * (x t).1 * ((R (x t)).1 - (x t).1) + 2 * (x t).2 * ((R (x t)).2 - (x t).2)) *
          Real.exp (11 * t) + g t * (Real.exp (11 * t) * 11)) t := by
      intro t ht
      have := (hg t ht).mul (((hasDerivAt_id t).const_mul 11).exp)
      simpa [k, mul_comm] using this
    have hkmono : MonotoneOn k (Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
      · exact fun t ht => (hk t ht).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        exact (hk t (le_of_lt ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        rw [(hk t (le_of_lt ht)).deriv]
        have e := Real.exp_pos (11 * t)
        set a := (x t).1; set b := (x t).2
        have c1 := clip_sq_le (2 * a - 2 * b)
        have c2 := clip_sq_le (2 * a + 2 * b)
        have hR1 : (R (x t)).1 = clip (2 * a - 2 * b) := rfl
        have hR2 : (R (x t)).2 = clip (2 * a + 2 * b) := rfl
        have hgt : g t = a ^ 2 + b ^ 2 := rfl
        rw [hR1, hR2, hgt]
        have : 0 ≤ 2 * a * (clip (2 * a - 2 * b) - a) + 2 * b * (clip (2 * a + 2 * b) - b) +
            (a ^ 2 + b ^ 2) * 11 := by
          nlinarith [sq_nonneg (a + clip (2 * a - 2 * b)), sq_nonneg (b + clip (2 * a + 2 * b))]
        nlinarith
    intro t ht
    have hk0 : k 0 ≤ k t := hkmono (le_refl (0:ℝ)) ht ht
    have : k 0 = g 0 := by simp [k]
    have hg0 : 0 < g 0 := sq_pos_of_ne h0
    have : 0 < k t := by linarith
    simp only [k] at this
    exact pos_of_mul_pos_left this (Real.exp_pos _).le
  -- Step B: near the origin `g' = 2 g ≥ 0`, so `g` cannot tend to `0`
  have hgt : Tendsto g atTop (𝓝 0) := by
    have hc : Continuous sq := by unfold sq; fun_prop
    simpa [g, sq] using (hc.tendsto 0).comp hlim
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp
    ((hgt.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/16))).and (eventually_ge_atTop 0))
  have hgmono : MonotoneOn g (Ici t₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici t₀) ?_ ?_ ?_
    · exact fun t ht => (hg t ((ht₀ t₀ le_rfl).2.trans ht)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hg t ((ht₀ t₀ le_rfl).2.trans (le_of_lt ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht' : t₀ ≤ t := le_of_lt ht
      rw [(hg t ((ht₀ t₀ le_rfl).2.trans ht')).deriv, R_linear (ht₀ t ht').1]
      simp only
      nlinarith [sq_nonneg (x t).1, sq_nonneg (x t).2]
  have hpos := hgpos t₀ (ht₀ t₀ le_rfl).2
  have : ∀ᶠ t in atTop, g t₀ / 2 < g t := by
    filter_upwards [eventually_ge_atTop t₀] with t ht
    have := hgmono (le_refl t₀) ht ht
    linarith
  obtain ⟨t, h1, h2⟩ :=
    (this.and (hgt.eventually (gt_mem_nhds (show (0:ℝ) < g t₀ / 2 by linarith)))).exists
  linarith

/-- A scalar relaxation `ẏ = a(t) - y` with targets `a(t) ∈ [-1, 1]` stays in `[-1, 1]`. -/
theorem scalar_relaxation_stays {y a : ℝ → ℝ} (hy : ∀ t, 0 ≤ t → HasDerivAt y (a t - y t) t)
    (ha : ∀ t, 0 ≤ t → a t ∈ Icc (-1 : ℝ) 1) (h0 : y 0 ∈ Icc (-1 : ℝ) 1) :
    ∀ t, 0 ≤ t → y t ∈ Icc (-1 : ℝ) 1 := by
  -- `(y - 1) eᵗ` is antitone and `(y + 1) eᵗ` is monotone on `[0, ∞)`
  have hk : ∀ c : ℝ, ∀ t, 0 ≤ t → HasDerivAt (fun s => (y s - c) * Real.exp s)
      ((a t - c) * Real.exp t) t := by
    intro c t ht
    have := ((hy t ht).sub_const c).mul (Real.hasDerivAt_exp t)
    convert this using 1; ring
  have hcont : ∀ c : ℝ, ContinuousOn (fun s => (y s - c) * Real.exp s) (Ici 0) := fun c t ht =>
    (hk c t ht).continuousAt.continuousWithinAt
  have hdiff : ∀ c : ℝ, DifferentiableOn ℝ (fun s => (y s - c) * Real.exp s) (interior (Ici 0)) :=
    fun c t ht => by
      rw [interior_Ici] at ht
      exact (hk c t (le_of_lt ht)).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn (fun s => (y s - 1) * Real.exp s) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (hcont 1) (hdiff 1) fun t ht => ?_
    rw [interior_Ici] at ht
    rw [(hk 1 t (le_of_lt ht)).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [(ha t (le_of_lt ht)).2])
      (Real.exp_pos t).le
  have hmono : MonotoneOn (fun s => (y s - (-1)) * Real.exp s) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (hcont (-1)) (hdiff (-1)) fun t ht => ?_
    rw [interior_Ici] at ht
    rw [(hk (-1) t (le_of_lt ht)).deriv]
    exact mul_nonneg (by linarith [(ha t (le_of_lt ht)).1]) (Real.exp_pos t).le
  intro t ht
  have h1 := hanti self_mem_Ici ht ht
  have h2 := hmono self_mem_Ici ht ht
  simp only [Real.exp_zero, mul_one] at h1 h2
  have he := Real.exp_pos t
  constructor
  · by_contra hlt
    push_neg at hlt
    have : (y t - -1) * Real.exp t < 0 := mul_neg_of_neg_of_pos (by linarith) he
    linarith [h0.1]
  · by_contra hlt
    push_neg at hlt
    have : 0 < (y t - 1) * Real.exp t := mul_pos (by linarith) he
    linarith [h0.2]

/-- **Proposition 7 (invariance).** Relaxation trajectories starting in the square stay in
the square, since `|Rᵢ| ≤ 1`. -/
theorem relaxation_stays_in_square {x : ℝ → ℝ × ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (R (x t) - x t) t) (h0 : x 0 ∈ square) :
    ∀ t, 0 ≤ t → x t ∈ square := by
  have h1 : ∀ t, 0 ≤ t → HasDerivAt (fun s => (x s).1) ((R (x t)).1 - (x t).1) t := fun t ht => by
    simpa using (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hx t ht)
  have h2 : ∀ t, 0 ≤ t → HasDerivAt (fun s => (x s).2) ((R (x t)).2 - (x t).2) t := fun t ht => by
    simpa using (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hx t ht)
  intro t ht
  exact ⟨scalar_relaxation_stays h1 (fun s _ => clip_mem _) h0.1 t ht,
    scalar_relaxation_stays h2 (fun s _ => clip_mem _) h0.2 t ht⟩

end TwoNodeLoop
