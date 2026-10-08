import Mathlib

/-!
# Two equilibria give the gradient (Theorem 13, Scellier–Bengio)

Slow variables `θ ∈ Θ`, states `x ∈ Xs`, energy `E(θ, x)`, cost `C(x)`, total energy
`F(θ, β, x) = E(θ, x) + β C(x)`. A branch `xb (θ, β)` of stationary points of `F(θ, β, ·)`
gives the free state `xb (θ, 0)` and the nudged state `xb (θ, β)`.
-/

open Set Filter Topology ContinuousLinearMap

noncomputable section

namespace EqProp

variable {Θ Xs : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup Xs] [NormedSpace ℝ Xs]

/-- Partial derivative in `θ` through the full derivative. -/
theorem fderiv_partial_fst {E : Θ × Xs → ℝ} (hE : Differentiable ℝ E) (θ : Θ) (x : Xs) :
    fderiv ℝ (fun θ' => E (θ', x)) θ = (fderiv ℝ E (θ, x)).comp (inl ℝ Θ Xs) :=
  ((hE (θ, x)).hasFDerivAt.comp θ (hasFDerivAt_prodMk_left θ x)).fderiv

/-- Partial derivative of `F` in `x` through the full derivatives. -/
theorem fderiv_partial_snd {E : Θ × Xs → ℝ} {C : Xs → ℝ} (hE : Differentiable ℝ E)
    (hC : Differentiable ℝ C) (θ : Θ) (β : ℝ) (x : Xs) :
    fderiv ℝ (fun x' => E (θ, x') + β * C x') x =
      (fderiv ℝ E (θ, x)).comp (inr ℝ Θ Xs) + β • fderiv ℝ C x := by
  have h1 := (hE (θ, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right θ x)
  have h2 := ((hC x).hasFDerivAt.const_mul β)
  exact (h1.add h2).fderiv

/-- **Theorem 13 (Two equilibria give the gradient; Scellier and Bengio).**
Let `E` be twice continuously differentiable and `C` differentiable, and let `xb` be
differentiable near `(θ₀, 0)` and select stationary points of the total energy:
`∂ₓ F(θ, β, xb(θ, β)) = 0` near `(θ₀, 0)`. Then the loss `J(θ) = C(xb(θ, 0))` is
differentiable at `θ₀`, and its derivative is the limit of the contrast
`(1/β) (∂E/∂θ(θ₀, xb(θ₀, β)) - ∂E/∂θ(θ₀, xb(θ₀, 0)))` as `β → 0`. -/
theorem two_equilibria_give_gradient {E : Θ × Xs → ℝ} {C : Xs → ℝ} {xb : Θ × ℝ → Xs}
    {θ₀ : Θ} (hE : ContDiff ℝ 2 E) (hC : Differentiable ℝ C)
    (hxb : ∀ᶠ p in 𝓝 (θ₀, (0 : ℝ)), DifferentiableAt ℝ xb p)
    (hstat : ∀ᶠ p in 𝓝 (θ₀, (0 : ℝ)),
      fderiv ℝ (fun x => E (p.1, x) + p.2 * C x) (xb p) = 0) :
    DifferentiableAt ℝ (fun θ => C (xb (θ, 0))) θ₀ ∧
    Tendsto (fun β : ℝ => β⁻¹ • (fderiv ℝ (fun θ => E (θ, xb (θ₀, β))) θ₀ -
        fderiv ℝ (fun θ => E (θ, xb (θ₀, 0))) θ₀))
      (𝓝[≠] 0) (𝓝 (fderiv ℝ (fun θ => C (xb (θ, 0))) θ₀)) := by
  set p₀ : Θ × ℝ := (θ₀, 0)
  have hEd : Differentiable ℝ E := hE.differentiable (by norm_num)
  have hDE : Differentiable ℝ (fderiv ℝ E) :=
    (hE.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hxb0 : DifferentiableAt ℝ xb p₀ := hxb.self_of_nhds
  -- the partial derivative `A p = ∂E/∂θ (p.1, xb p)` and the cost along the branch
  set A : Θ × ℝ → (Θ →L[ℝ] ℝ) := fun p => (fderiv ℝ E (p.1, xb p)).comp (inl ℝ Θ Xs)
  set c : Θ × ℝ → ℝ := fun p => C (xb p)
  have hpair : ∀ p, DifferentiableAt ℝ xb p →
      HasFDerivAt (fun q : Θ × ℝ => (q.1, xb q)) ((fst ℝ Θ ℝ).prod (fderiv ℝ xb p)) p :=
    fun p hp => hasFDerivAt_fst.prodMk hp.hasFDerivAt
  have hA : DifferentiableAt ℝ A p₀ :=
    ((hDE _).comp p₀ (hpair p₀ hxb0).differentiableAt).clm_comp (differentiableAt_const _)
  have hc : ∀ p, DifferentiableAt ℝ xb p → HasFDerivAt c ((fderiv ℝ C (xb p)).comp
      (fderiv ℝ xb p)) p := fun p hp => (hC _).hasFDerivAt.comp p hp.hasFDerivAt
  -- `G p = F(p.1, p.2, xb p)` has derivative `G' p = A p ∘ fst + c p • snd`
  set G : Θ × ℝ → ℝ := fun p => E (p.1, xb p) + p.2 * C (xb p)
  set G' : Θ × ℝ → (Θ × ℝ →L[ℝ] ℝ) := fun p => (A p).comp (fst ℝ Θ ℝ) + c p • snd ℝ Θ ℝ
  have hG : ∀ᶠ p in 𝓝 p₀, HasFDerivAt G (G' p) p := by
    filter_upwards [hxb, hstat] with p hp hs
    rw [fderiv_partial_snd hEd hC] at hs
    have h1 := (hEd _).hasFDerivAt.comp p (hpair p hp)
    have h2 := (hasFDerivAt_snd (p := p)).mul (hc p hp)
    convert h1.add h2 using 1
    refine ContinuousLinearMap.ext fun w => ?_
    have := congrArg (fun L => L (fderiv ℝ xb p w)) hs
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp,
      ContinuousLinearMap.smul_apply, smul_eq_mul, inr_apply,
      ContinuousLinearMap.zero_apply] at this
    have hsplit : (w.1, fderiv ℝ xb p w) = ((w.1, (0 : Xs)) + (0, fderiv ℝ xb p w) : Θ × Xs) := by
      simp
    simp only [G', A, c, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
      Function.comp, smul_eq_mul, inl_apply, coe_fst', coe_snd', prod_apply,
      ContinuousLinearMap.smul_apply, hsplit, map_add]
    linarith
  -- `G'` is differentiable at `p₀`; symmetry of the second derivative
  have hcd : DifferentiableAt ℝ c p₀ := (hc p₀ hxb0).differentiableAt
  have hG'd : DifferentiableAt ℝ G' p₀ :=
    (hA.clm_comp (differentiableAt_const _)).add (hcd.smul_const _)
  set G'' := fderiv ℝ G' p₀
  have hsymm := second_derivative_symmetric_of_eventually hG hG'd.hasFDerivAt
  -- the `β`-direction: `G' p (0, 1) = c p`
  set w : Θ × ℝ := (0, 1)
  have hGw : HasFDerivAt c (G''.flip w) p₀ := by
    have h := hG'd.hasFDerivAt.clm_apply (hasFDerivAt_const w p₀)
    have hfun : (fun p => G' p w) = c := by
      funext p; simp [G', w]
    rw [hfun] at h
    simpa using h
  -- the loss `J θ = c (θ, 0)`
  set DJ : Θ →L[ℝ] ℝ := (G''.flip w).comp (inl ℝ Θ ℝ)
  have hJ : HasFDerivAt (fun θ => C (xb (θ, 0))) DJ θ₀ := by
    have h := (hasFDerivAt_prodMk_left (𝕜 := ℝ) θ₀ (0 : ℝ))
    exact hGw.comp θ₀ h
  refine ⟨hJ.differentiableAt, ?_⟩
  rw [hJ.fderiv]
  -- the `θ`-directions: `G' p (v, 0) = A p v`
  have hAv : ∀ v : Θ, G'' w (v, 0) = fderiv ℝ A p₀ w v := by
    intro v
    have h1 := hG'd.hasFDerivAt.clm_apply (hasFDerivAt_const ((v, 0) : Θ × ℝ) p₀)
    have h2 := hA.hasFDerivAt.clm_apply (hasFDerivAt_const v p₀)
    have hfun : (fun p => G' p (v, 0)) = fun p => A p v := by
      funext p; simp [G']
    rw [hfun] at h1
    have := congrArg (fun L => L w) (h1.unique h2)
    simpa using this
  have hAw : fderiv ℝ A p₀ w = DJ := by
    ext v
    rw [← hAv, ← hsymm]
    simp [DJ]; rfl
  -- the contrast is the slope of `β ↦ A (θ₀, β)`
  have hline : HasDerivAt (fun β : ℝ => ((θ₀, β) : Θ × ℝ)) w 0 :=
    (hasDerivAt_const (0 : ℝ) θ₀).prodMk (hasDerivAt_id 0)
  have hh : HasDerivAt (fun β : ℝ => A (θ₀, β)) DJ 0 := by
    have := hA.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
    rwa [hAw] at this
  have hslope := hasDerivAt_iff_tendsto_slope.mp hh
  refine hslope.congr' (Eventually.of_forall fun β => ?_)
  simp only [slope_def_module, sub_zero, fderiv_partial_fst hEd, A]
  rfl

/-- **No surprise, no learning.** If the free state `x₀` is stationary for the energy and
the cost is also stationary there (`∇ₓ C(x₀) = 0`), then `x₀` is a stationary point of the
nudged energy `F(θ, β, ·)` for every `β`. -/
theorem free_state_stationary_nudged {E : Θ × Xs → ℝ} {C : Xs → ℝ} (hE : Differentiable ℝ E)
    (hC : Differentiable ℝ C) {θ : Θ} {x₀ : Xs}
    (hfree : fderiv ℝ (fun x => E (θ, x)) x₀ = 0) (hsurp : fderiv ℝ C x₀ = 0) (β : ℝ) :
    fderiv ℝ (fun x => E (θ, x) + β * C x) x₀ = 0 := by
  rw [fderiv_partial_snd hE hC, hsurp, smul_zero, add_zero]
  rw [← ((hE (θ, x₀)).hasFDerivAt.comp x₀ (hasFDerivAt_prodMk_right θ x₀)).fderiv]
  exact hfree

/-- **No surprise, no learning (contrast).** If moreover the stationary branch is locally
unique — every stationary point of `F(θ, β, ·)` in a set `U ∋ x₀` equals `xb β` — then the nudged state equals the free state and the two-state contrast
`(η/β) (∂E/∂θ(θ, xb β) - ∂E/∂θ(θ, x₀))` vanishes. -/
theorem no_surprise_no_learning {E : Θ × Xs → ℝ} {C : Xs → ℝ} (hE : Differentiable ℝ E)
    (hC : Differentiable ℝ C) {θ : Θ} {x₀ : Xs} {U : Set Xs} (hx₀ : x₀ ∈ U)
    (hfree : fderiv ℝ (fun x => E (θ, x)) x₀ = 0) (hsurp : fderiv ℝ C x₀ = 0)
    {xb : ℝ → Xs}
    (huniq : ∀ β, ∀ x ∈ U, fderiv ℝ (fun x => E (θ, x) + β * C x) x = 0 → x = xb β)
    (β η : ℝ) :
    xb β = x₀ ∧ (η / β) • (fderiv ℝ (fun θ' => E (θ', xb β)) θ -
      fderiv ℝ (fun θ' => E (θ', x₀)) θ) = 0 := by
  have h := (huniq β x₀ hx₀ (free_state_stationary_nudged hE hC hfree hsurp β)).symm
  refine ⟨h, ?_⟩
  rw [h, sub_self, smul_zero]

/-- **Pairwise energy.** For a pairwise energy `E(θ, s) = -∑_{(i,j) ∈ P} θᵢⱼ sᵢ sⱼ + E₀(s)`
with one parameter per pair, `∂E/∂θᵢⱼ = -sᵢ sⱼ`; hence the two-state contrast for the pair
`(i, j)` is `(η/β) ((sᵢ sⱼ)^{nudged} - (sᵢ sⱼ)^{free})` up to sign convention
`Δθ = -(η/β) (∂E/∂θ(nudged) - ∂E/∂θ(free))`. -/
theorem pairwise_energy_partial {ι : Type*} [DecidableEq ι] (P : Finset (ι × ι))
    (E₀ : (ι → ℝ) → ℝ) (s : ι → ℝ) (θ : ι × ι → ℝ) (q : ι × ι) (hq : q ∈ P) :
    HasDerivAt (fun t : ℝ => -∑ r ∈ P, Function.update θ q t r * s r.1 * s r.2 + E₀ s)
      (-(s q.1 * s q.2)) (θ q) := by
  have : (fun t : ℝ => -∑ r ∈ P, Function.update θ q t r * s r.1 * s r.2 + E₀ s) =
      fun t => -(t * s q.1 * s q.2 + ∑ r ∈ P.erase q, θ r * s r.1 * s r.2) + E₀ s := by
    funext t
    rw [← Finset.add_sum_erase P _ hq]
    have hs : ∑ r ∈ P.erase q, Function.update θ q t r * s r.1 * s r.2 =
        ∑ r ∈ P.erase q, θ r * s r.1 * s r.2 :=
      Finset.sum_congr rfl fun r hr => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hr)]
    rw [hs]
    simp
  rw [this]
  have h := (((hasDerivAt_id (θ q)).mul_const (s q.1)).mul_const (s q.2)).add_const
    (∑ r ∈ P.erase q, θ r * s r.1 * s r.2)
  convert (h.neg).add_const (E₀ s) using 1
  simp

/-- **Two speeds, one mechanism.** If states and slow variables follow
`ẋ = -Mₓ ∇ₓF`, `θ̇ = -ε M_θ ∇_θF` with positive semidefinite mobilities and `ε ≥ 0`, then
`Ḟ = -⟪∇ₓF, Mₓ ∇ₓF⟫ - ε ⟪∇_θF, M_θ ∇_θF⟫ ≤ 0`. -/
theorem two_speed_dissipation {Eθ Ex : Type*} [NormedAddCommGroup Eθ] [InnerProductSpace ℝ Eθ]
    [NormedAddCommGroup Ex] [InnerProductSpace ℝ Ex] {F : Eθ × Ex → ℝ}
    {θ : ℝ → Eθ} {x : ℝ → Ex} {gθ : ℝ → Eθ} {gx : ℝ → Ex} {Mθ : Eθ →L[ℝ] Eθ}
    {Mx : Ex →L[ℝ] Ex} {ε t : ℝ} (hε : 0 ≤ ε)
    (hMθ : ∀ v, 0 ≤ inner ℝ v (Mθ v)) (hMx : ∀ v, 0 ≤ inner ℝ v (Mx v))
    (hF : HasFDerivAt F ((innerSL ℝ (gθ t)).comp (fst ℝ Eθ Ex) +
      (innerSL ℝ (gx t)).comp (snd ℝ Eθ Ex)) (θ t, x t))
    (hθ : HasDerivAt θ (-(ε • Mθ (gθ t))) t) (hx : HasDerivAt x (-(Mx (gx t))) t) :
    HasDerivAt (fun s => F (θ s, x s))
      (-inner ℝ (gx t) (Mx (gx t)) - ε * inner ℝ (gθ t) (Mθ (gθ t))) t ∧
    -inner ℝ (gx t) (Mx (gx t)) - ε * inner ℝ (gθ t) (Mθ (gθ t)) ≤ 0 := by
  constructor
  · have := hF.comp_hasDerivAt t (hθ.prodMk hx)
    convert this using 1
    simp [inner_neg_right, inner_smul_right]
    ring
  · have := hMθ (gθ t)
    have := hMx (gx t)
    nlinarith

end EqProp
