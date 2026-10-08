import RequestProject.Defs

/-!
# Reachability under contraction (Theorem 5) and displacement bounds (Theorem 12)

Everything is stated for a self-map `R` of a subset `X` of a normed space `E` (for a repair
network, `R = fun x => net.globalR x e` and `X = net.space`).
-/

open Set Filter Topology

noncomputable section

namespace Repair

variable {E : Type*} [NormedAddCommGroup E]

/-- `R` contracts distances by the factor `q` on `X`. -/
def ContractsOn (R : E → E) (X : Set E) (q : ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, ‖R x - R y‖ ≤ q * ‖x - y‖

/-- **Theorem 5 (1): existence and uniqueness** (Banach). -/
theorem contraction_existsUnique_fixedPoint [CompleteSpace E] {R : E → E} {X : Set E}
    {q : ℝ} (hXne : X.Nonempty) (hXc : IsClosed X) (hRX : MapsTo R X X)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hR : ContractsOn R X q) :
    ∃! x, x ∈ X ∧ R x = x := by
  haveI : CompleteSpace X := hXc.completeSpace_coe
  haveI : Nonempty X := hXne.to_subtype
  set f : X → X := hRX.restrict R X X
  have hf : ContractingWith ⟨q, hq0⟩ f := by
    refine ⟨by exact_mod_cast hq1, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    simp only [Subtype.dist_eq, dist_eq_norm, f, MapsTo.val_restrict_apply]
    exact hR a a.2 b b.2
  obtain ⟨p, hp⟩ : ∃ p, f p = p := ⟨_, hf.fixedPoint_isFixedPt (f := f)⟩
  refine ⟨p, ⟨p.2, congrArg Subtype.val hp⟩, ?_⟩
  rintro y ⟨hyX, hy⟩
  have h1 : ‖y - (p : E)‖ ≤ q * ‖y - p‖ := by
    have := hR y hyX p p.2
    rwa [hy, show R p = p from congrArg Subtype.val hp] at this
  have : ‖y - (p : E)‖ = 0 := by
    have hn := norm_nonneg (y - (p : E))
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- One damped step contracts with factor `1 - η + η q` towards a fixed point. -/
theorem dampedStep_dist [NormedSpace ℝ E] {R : E → E} {X : Set E} {q η : ℝ} (hR : ContractsOn R X q)
    (h0 : 0 ≤ η) (h1 : η ≤ 1) {x xs : E} (hx : x ∈ X) (hxs : xs ∈ X) (hfix : R xs = xs) :
    ‖dampedStep R η x - xs‖ ≤ (1 - η + η * q) * ‖x - xs‖ := by
  have : dampedStep R η x - xs = (1 - η) • (x - xs) + η • (R x - R xs) := by
    unfold dampedStep; rw [hfix]; module
  rw [this]
  calc ‖(1 - η) • (x - xs) + η • (R x - R xs)‖
      ≤ ‖(1 - η) • (x - xs)‖ + ‖η • (R x - R xs)‖ := norm_add_le _ _
    _ = (1 - η) * ‖x - xs‖ + η * ‖R x - R xs‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg h0]
    _ ≤ (1 - η) * ‖x - xs‖ + η * (q * ‖x - xs‖) := by
        gcongr; exact hR x hx xs hxs
    _ = (1 - η + η * q) * ‖x - xs‖ := by ring

/-- **Theorem 5 (2): damped repair converges geometrically.** With `η = 1` this is
synchronous repair (`damped_one`). -/
theorem damped_dist_le [NormedSpace ℝ E] {R : E → E} {X : Set E} {q η : ℝ} (hX : Convex ℝ X)
    (hRX : MapsTo R X X) (hR : ContractsOn R X q) (h0 : 0 < η) (h1 : η ≤ 1)
    (hq0 : 0 ≤ q) {x₀ xs : E} (hx₀ : x₀ ∈ X) (hxs : xs ∈ X) (hfix : R xs = xs) (t : ℕ) :
    ‖damped R η x₀ t - xs‖ ≤ (1 - η + η * q) ^ t * ‖x₀ - xs‖ := by
  induction t with
  | zero => simp [damped]
  | succ t ih =>
    have hc : 0 ≤ 1 - η + η * q := by nlinarith
    calc ‖damped R η x₀ (t + 1) - xs‖
        ≤ (1 - η + η * q) * ‖damped R η x₀ t - xs‖ :=
          dampedStep_dist hR h0.le h1 (damped_mem hX hRX h0.le h1 hx₀ t) hxs hfix
      _ ≤ (1 - η + η * q) * ((1 - η + η * q) ^ t * ‖x₀ - xs‖) := by gcongr
      _ = (1 - η + η * q) ^ (t + 1) * ‖x₀ - xs‖ := by ring

/-- **Theorem 5 (2), convergence.** Damped (in particular synchronous) repair converges
to the fixed point from every start in `X`. -/
theorem damped_tendsto [NormedSpace ℝ E] {R : E → E} {X : Set E} {q η : ℝ} (hX : Convex ℝ X)
    (hRX : MapsTo R X X) (hR : ContractsOn R X q) (h0 : 0 < η) (h1 : η ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) {x₀ xs : E} (hx₀ : x₀ ∈ X) (hxs : xs ∈ X)
    (hfix : R xs = xs) : Tendsto (damped R η x₀) atTop (𝓝 xs) := by
  have hc0 : 0 ≤ 1 - η + η * q := by nlinarith
  have hc1 : 1 - η + η * q < 1 := by nlinarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _)
    (damped_dist_le hX hRX hR h0 h1 hq0 hx₀ hxs hfix) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const ‖x₀ - xs‖

/-- **Theorem 5 (3): relaxation converges exponentially.** If `x` solves
`ẋ = R(x) - x` on `[0, ∞)` and stays in `X`, then
`‖x(t) - x⋆‖ ≤ exp(-(1-q) t) ‖x(0) - x⋆‖`. -/
theorem relaxation_dist_le [NormedSpace ℝ E] {R : E → E} {X : Set E} {q : ℝ} (hR : ContractsOn R X q)
    {x : ℝ → E} (hx : ∀ t, 0 ≤ t → HasDerivAt x (R (x t) - x t) t)
    (hxX : ∀ t, 0 ≤ t → x t ∈ X) {xs : E} (hxs : xs ∈ X) (hfix : R xs = xs) {t : ℝ}
    (ht : 0 ≤ t) : ‖x t - xs‖ ≤ Real.exp (-(1 - q) * t) * ‖x 0 - xs‖ := by
  -- `w s = exp s • (x s - xs)` satisfies `ẇ = exp s • (R (x s) - R xs)`.
  set w : ℝ → E := fun s => Real.exp s • (x s - xs) with hw
  have hwd : ∀ s, 0 ≤ s → HasDerivAt w (Real.exp s • (R (x s) - R xs)) s := by
    intro s hs
    have h := (Real.hasDerivAt_exp s).smul ((hx s hs).sub_const xs)
    convert h using 1
    rw [hfix, smul_sub, smul_sub, smul_sub]; abel
  have hbound : ∀ s ∈ Ico (0 : ℝ) t, ‖Real.exp s • (R (x s) - R xs)‖ ≤ q * ‖w s‖ + 0 := by
    intro s hs
    rw [norm_smul, add_zero, hw]; dsimp only
    rw [norm_smul]
    have := hR (x s) (hxX s hs.1) xs hxs
    have he : 0 ≤ ‖Real.exp s‖ := norm_nonneg _
    nlinarith
  have hcont : ContinuousOn w (Icc 0 t) := fun s hs =>
    (hwd s hs.1).continuousAt.continuousWithinAt
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := w) (a := 0) (b := t)
    (δ := ‖w 0‖) (K := q) (ε := 0) hcont
    (fun s hs => (hwd s hs.1).hasDerivWithinAt) le_rfl hbound t ⟨ht, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at hg
  have hw0 : ‖w 0‖ = ‖x 0 - xs‖ := by simp [hw]
  have hwt : ‖w t‖ = Real.exp t * ‖x t - xs‖ := by
    simp [hw, norm_smul, Real.norm_of_nonneg (Real.exp_pos t).le]
  rw [hwt, hw0] at hg
  have hexp : Real.exp (-(1 - q) * t) = Real.exp (q * t) / Real.exp t := by
    rw [← Real.exp_sub]; ring_nf
  rw [hexp, div_mul_eq_mul_div, le_div_iff₀ (Real.exp_pos t)]
  nlinarith [Real.exp_pos t]

/-- **Theorem 5 (4): sensitivity to evidence.** If `x⋆(e)` and `x⋆(e')` are equilibria
under `e` and `e'`, `R(·, e)` contracts with factor `q < 1`, and `R` is `L`-Lipschitz in the
evidence, then `‖x⋆(e) - x⋆(e')‖ ≤ L ‖e - e'‖ / (1 - q)`. -/
theorem fixedPoint_lipschitz_evidence {F : Type*} [NormedAddCommGroup F]
    {R : E → F → E} {X : Set E} {q L : ℝ} {e e' : F} (hq1 : q < 1)
    (hR : ContractsOn (fun x => R x e) X q)
    (hL : ∀ x ∈ X, ‖R x e - R x e'‖ ≤ L * ‖e - e'‖)
    {xs xs' : E} (hxs : xs ∈ X) (hxs' : xs' ∈ X) (hfix : R xs e = xs) (hfix' : R xs' e' = xs') :
    ‖xs - xs'‖ ≤ L * ‖e - e'‖ / (1 - q) := by
  rw [le_div_iff₀ (by linarith)]
  have h1 : ‖xs - xs'‖ ≤ ‖R xs e - R xs' e‖ + ‖R xs' e - R xs' e'‖ := by
    calc ‖xs - xs'‖ = ‖(R xs e - R xs' e) + (R xs' e - R xs' e')‖ := by
          rw [hfix, hfix']; abel_nf
      _ ≤ _ := norm_add_le _ _
  have := hR xs hxs xs' hxs'
  have := hL xs' hxs'
  nlinarith

/-- **Theorem 12 (Equilibrium displacement is bounded by disagreement on both sides).**
If `x⋆` is a fixed point of `R` which contracts with factor `0 ≤ q < 1`, then for any
state `x` with disagreement `D = ‖R x - x‖`,
`D / (1 + q) ≤ ‖x⋆ - x‖ ≤ D / (1 - q)`. -/
theorem displacement_bounds {R : E → E} {X : Set E} {q : ℝ} (hR : ContractsOn R X q)
    (hq0 : 0 ≤ q) (hq1 : q < 1) {xs x : E} (hxs : xs ∈ X) (hx : x ∈ X) (hfix : R xs = xs) :
    ‖R x - x‖ / (1 + q) ≤ ‖xs - x‖ ∧ ‖xs - x‖ ≤ ‖R x - x‖ / (1 - q) := by
  have hc := hR xs hxs x hx
  rw [hfix] at hc
  constructor
  · rw [div_le_iff₀ (by linarith)]
    have : ‖R x - x‖ ≤ ‖R x - xs‖ + ‖xs - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [norm_sub_rev (R x) xs] at this
    nlinarith
  · rw [le_div_iff₀ (by linarith)]
    have : ‖xs - x‖ ≤ ‖xs - R x‖ + ‖R x - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    nlinarith

/-- **Detuning bound (Section 2).** If the map under the new evidence contracts with
factor `q` and has rest `x⋆`, its distance from the reference rest `x₀` lies between
`Δ/(1+q)` and `Δ/(1-q)`, where `Δ = ‖R x₀ - x₀‖` is the detuning; in particular the two rests
coincide iff `Δ = 0`. -/
theorem detuning_zero_iff {R : E → E} {X : Set E} {q : ℝ} (hR : ContractsOn R X q)
    (hq0 : 0 ≤ q) (hq1 : q < 1) {xs x₀ : E} (hxs : xs ∈ X) (hx₀ : x₀ ∈ X) (hfix : R xs = xs) :
    xs = x₀ ↔ ‖R x₀ - x₀‖ = 0 := by
  obtain ⟨h1, h2⟩ := displacement_bounds hR hq0 hq1 hxs hx₀ hfix
  constructor
  · rintro rfl; simp [hfix]
  · intro h
    rw [h, zero_div] at h2
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)

end Repair

/-! ### Specialisation to repair networks -/

namespace RepairNet

variable {V : Type*} [Fintype V] {d : V → ℕ} (net : RepairNet V d)

/-- **Theorem 5 (1) for repair networks.** If every node's state space is closed and
nonempty and `R(·, e)` contracts on `X`, the network has exactly one equilibrium under `e`. -/
theorem existsUnique_equilibrium_of_contraction (e : net.Evidence) {q : ℝ}
    (hne : ∀ i, (net.X i).Nonempty) (hcl : ∀ i, IsClosed (net.X i)) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hR : Repair.ContractsOn (fun x => net.globalR x e) net.space q) :
    ∃! x, net.IsEquilibrium x e :=
  Repair.contraction_existsUnique_fixedPoint (Set.univ_pi_nonempty_iff.mpr hne)
    (isClosed_set_pi fun i _ => hcl i) (net.globalR_mapsTo e) hq0 hq1 hR

/-- **Theorem 12 for repair networks.** With `x` the old agreement and `e'` the new
evidence, the new equilibrium lies at distance between `D/(1+q)` and `D/(1-q)` from `x`,
where `D = D(x, e')` is the network's disagreement at `x`. -/
theorem equilibrium_displacement (e' : net.Evidence) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hR : Repair.ContractsOn (fun x => net.globalR x e') net.space q)
    {xs x : RepairNetwork.State d} (hxs : net.IsEquilibrium xs e') (hx : x ∈ net.space) :
    net.disagreement x e' / (1 + q) ≤ ‖xs - x‖ ∧ ‖xs - x‖ ≤ net.disagreement x e' / (1 - q) :=
  Repair.displacement_bounds hR hq0 hq1 hxs.1 hx hxs.2

end RepairNet
