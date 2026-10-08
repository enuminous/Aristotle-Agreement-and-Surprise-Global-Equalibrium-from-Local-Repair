import Mathlib

/-!
# Equilibrium limit points under a potential (Theorem 6)

Nodes `i : Fin n` hold states in compact sets `X i` of metric spaces `S i`. A continuous
potential `Φ` has, for every node and every state of the other nodes, a unique minimiser in
`X i`, which is the repair target `R i x`. Nodes repair one at a time in the cyclic order
`0, 1, …, n-1, 0, 1, …`.
-/

open Set Filter Topology Function

noncomputable section

namespace PotentialRepair

variable {n : ℕ} [NeZero n] {S : Fin n → Type*} [∀ i, MetricSpace (S i)]

/-- The node repaired at step `k` of the cyclic order. -/
def phase (n : ℕ) [NeZero n] (k : ℕ) : Fin n := ⟨k % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩

/-- Cyclic coordinate repair: at step `k` node `k mod n` replaces its state by its target. -/
def cyclic (R : ∀ i, (∀ j, S j) → S i) (x₀ : ∀ j, S j) : ℕ → ∀ j, S j
  | 0 => x₀
  | k + 1 => update (cyclic R x₀ k) (phase n k) (R (phase n k) (cyclic R x₀ k))

/-- Hypotheses of Theorem 6: `R i x ∈ X i` is the unique minimiser of `y ↦ Φ(update x i y)`
on `X i`, for every `x ∈ X`. -/
def UniqueMinimisers (X : ∀ i, Set (S i)) (Φ : (∀ i, S i) → ℝ) (R : ∀ i, (∀ j, S j) → S i) :
    Prop :=
  ∀ i, ∀ x ∈ Set.pi univ X, R i x ∈ X i ∧
    ∀ y ∈ X i, y ≠ R i x → Φ (update x i (R i x)) < Φ (update x i y)

variable {X : ∀ i, Set (S i)} {Φ : (∀ i, S i) → ℝ} {R : ∀ i, (∀ j, S j) → S i}

omit [NeZero n] [∀ i, MetricSpace (S i)] in
theorem update_mem {x : ∀ i, S i} (hx : x ∈ Set.pi univ X) (i : Fin n) {y : S i}
    (hy : y ∈ X i) : update x i y ∈ Set.pi univ X := by
  intro j _
  rcases eq_or_ne j i with rfl | h
  · simpa using hy
  · simpa [h] using hx j (mem_univ _)

omit [NeZero n] [∀ i, MetricSpace (S i)] in
theorem minimiser_le (hR : UniqueMinimisers X Φ R) {x : ∀ i, S i} (hx : x ∈ Set.pi univ X)
    (i : Fin n) {y : S i} (hy : y ∈ X i) : Φ (update x i (R i x)) ≤ Φ (update x i y) := by
  by_cases h : y = R i x
  · rw [h]
  · exact ((hR i x hx).2 y hy h).le

omit [∀ i, MetricSpace (S i)] in
theorem cyclic_mem (hR : UniqueMinimisers X Φ R) {x₀ : ∀ i, S i} (hx₀ : x₀ ∈ Set.pi univ X)
    (k : ℕ) : cyclic R x₀ k ∈ Set.pi univ X := by
  induction k with
  | zero => exact hx₀
  | succ k ih => exact update_mem ih _ (hR _ _ ih).1

omit [∀ i, MetricSpace (S i)] in
/-- **Theorem 6, monotonicity.** `Φ` never increases along cyclic repair. -/
theorem cyclic_antitone (hR : UniqueMinimisers X Φ R) {x₀ : ∀ i, S i}
    (hx₀ : x₀ ∈ Set.pi univ X) : Antitone fun k => Φ (cyclic R x₀ k) := by
  refine antitone_nat_of_succ_le fun k => ?_
  have hk := cyclic_mem hR hx₀ k
  have := minimiser_le hR hk (phase n k) (hk (phase n k) (mem_univ _))
  simpa [cyclic] using this

omit [NeZero n] in
/-- `Φ` along a convergent sequence in `X`. -/
theorem tendsto_Φ (hΦ : ContinuousOn Φ (Set.pi univ X)) {u : ℕ → ∀ i, S i}
    (hu : ∀ m, u m ∈ Set.pi univ X) {q : ∀ i, S i} (hq : q ∈ Set.pi univ X)
    (hlim : Tendsto u atTop (𝓝 q)) : Tendsto (fun m => Φ (u m)) atTop (𝓝 (Φ q)) :=
  (hΦ q hq).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hu⟩)

omit [NeZero n] in
/-- A limit of repair targets along a convergent sequence is the repair target of the limit. -/
theorem limit_of_targets (hX : ∀ i, IsCompact (X i)) (hΦ : ContinuousOn Φ (Set.pi univ X))
    (hR : UniqueMinimisers X Φ R) (i : Fin n) {u : ℕ → ∀ i, S i}
    (hu : ∀ m, u m ∈ Set.pi univ X) {x : ∀ i, S i} (hx : x ∈ Set.pi univ X)
    (hlim : Tendsto u atTop (𝓝 x)) {a : S i} (ha : a ∈ X i)
    (hRa : Tendsto (fun m => R i (u m)) atTop (𝓝 a)) : a = R i x := by
  have hclosed : IsClosed (X i) := (hX i).isClosed
  -- `a` minimises `Φ (update x i ·)` on `X i`
  have hmin : ∀ z ∈ X i, Φ (update x i a) ≤ Φ (update x i z) := by
    intro z hz
    have h1 := tendsto_Φ hΦ (fun m => update_mem (hu m) i (hR i _ (hu m)).1)
      (update_mem hx i ha) (hlim.update i hRa)
    have h2 := tendsto_Φ hΦ (fun m => update_mem (hu m) i hz)
      (update_mem hx i hz) (hlim.update i tendsto_const_nhds)
    exact le_of_tendsto_of_tendsto' h1 h2 fun m => minimiser_le hR (hu m) i hz
  by_contra hne
  have := (hR i x hx).2 a ha hne
  have := hmin _ (hR i x hx).1
  linarith

omit [NeZero n] in
/-- Repair targets depend continuously on the state (uniqueness of the minimiser and
compactness). -/
theorem tendsto_target (hX : ∀ i, IsCompact (X i)) (hΦ : ContinuousOn Φ (Set.pi univ X))
    (hR : UniqueMinimisers X Φ R) (i : Fin n) {u : ℕ → ∀ i, S i}
    (hu : ∀ m, u m ∈ Set.pi univ X) {x : ∀ i, S i} (hx : x ∈ Set.pi univ X)
    (hlim : Tendsto u atTop (𝓝 x)) : Tendsto (fun m => R i (u m)) atTop (𝓝 (R i x)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨a, ha, φ, hφ, hlimφ⟩ :=
    (hX i).tendsto_subseq (x := fun m => R i (u (ns m))) fun m => (hR i _ (hu (ns m))).1
  refine ⟨φ, ?_⟩
  have hsub : Tendsto (fun m => u (ns (φ m))) atTop (𝓝 x) :=
    hlim.comp (hns.comp hφ.tendsto_atTop)
  have := limit_of_targets hX hΦ hR i (fun m => hu (ns (φ m))) hx hsub ha hlimφ
  rw [← this]
  exact hlimφ

/-- **Theorem 6 (Equilibrium limit points under a potential).** Under unique coordinate
minimisers of a continuous potential on a product of compact sets, every limit point of
cyclic repair is an equilibrium: it lies in `X` and every node holds its repair target. -/
theorem limit_point_is_equilibrium (hX : ∀ i, IsCompact (X i))
    (hΦ : ContinuousOn Φ (Set.pi univ X)) (hR : UniqueMinimisers X Φ R) {x₀ : ∀ i, S i}
    (hx₀ : x₀ ∈ Set.pi univ X) {p : ∀ i, S i} (hp : MapClusterPt p atTop (cyclic R x₀)) :
    p ∈ Set.pi univ X ∧ ∀ i, R i p = p i := by
  set x := cyclic R x₀
  have hU : IsCompact (Set.pi univ X) := isCompact_univ_pi hX
  have hxU : ∀ k, x k ∈ Set.pi univ X := cyclic_mem hR hx₀
  -- `Φ (x k)` converges, to `Φ∞`
  obtain ⟨Φinf, hΦinf⟩ : ∃ L, Tendsto (fun k => Φ (x k)) atTop (𝓝 L) := by
    have hbdd : BddBelow (range fun k => Φ (x k)) := by
      obtain ⟨b, hb⟩ := hU.bddBelow_image hΦ
      exact ⟨b, by rintro _ ⟨k, rfl⟩; exact hb ⟨x k, hxU k, rfl⟩⟩
    exact ⟨_, tendsto_atTop_ciInf (cyclic_antitone hR hx₀) hbdd⟩
  obtain ⟨ψ, hψ, hψlim⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hp
  have hpU : p ∈ Set.pi univ X :=
    hU.isClosed.mem_of_tendsto hψlim (Eventually.of_forall fun m => hxU (ψ m))
  refine ⟨hpU, ?_⟩
  -- key step: along indices of a fixed phase `r` converging to `p`, node `r` is at rest
  -- at `p` and the following states also converge to `p`
  have key : ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop → ∀ r : ℕ, (∀ m, φ m % n = r % n) →
      Tendsto (fun m => x (φ m)) atTop (𝓝 p) →
      R (phase n r) p = p (phase n r) ∧ Tendsto (fun m => x (φ m + 1)) atTop (𝓝 p) := by
    intro φ hφ r hr hlim
    have hph : ∀ m, phase n (φ m) = phase n r := fun m => Fin.ext (by simp [phase, hr m])
    have hstep : ∀ m, x (φ m + 1) = update (x (φ m)) (phase n r) (R (phase n r) (x (φ m))) := by
      intro m; change cyclic R x₀ (φ m + 1) = _; rw [cyclic, hph m]
    set q := update p (phase n r) (R (phase n r) p)
    have hqU : q ∈ Set.pi univ X := update_mem hpU _ (hR _ _ hpU).1
    have hlimq : Tendsto (fun m => x (φ m + 1)) atTop (𝓝 q) := by
      simp only [hstep]
      exact hlim.update _ (tendsto_target hX hΦ hR _ (fun m => hxU (φ m)) hpU hlim)
    have h1 : Φ p = Φinf := tendsto_nhds_unique
      (tendsto_Φ hΦ (fun m => hxU (φ m)) hpU hlim) (hΦinf.comp hφ)
    have h2 : Φ q = Φinf := tendsto_nhds_unique
      (tendsto_Φ hΦ (fun m => hxU (φ m + 1)) hqU hlimq)
      (hΦinf.comp ((tendsto_add_atTop_nat 1).comp hφ))
    have hfix : R (phase n r) p = p (phase n r) := by
      by_contra hne
      have := (hR _ p hpU).2 (p (phase n r)) (hpU _ (mem_univ _)) (Ne.symm hne)
      rw [update_eq_self] at this
      change Φ q < Φ p at this
      linarith
    refine ⟨hfix, ?_⟩
    have : q = p := by simp only [q, hfix, update_eq_self]
    rwa [this] at hlimq
  -- pick a phase that occurs infinitely often along `ψ`
  obtain ⟨r, hr⟩ : ∃ r : Fin n, ∃ᶠ m in atTop, phase n (ψ m) = r := by
    by_contra h
    push_neg at h
    have : ∀ᶠ m in atTop, ∀ r : Fin n, phase n (ψ m) ≠ r := by
      rw [eventually_all]; intro r; exact (h r).mono fun m hm => hm
    obtain ⟨m, hm⟩ := this.exists
    exact hm _ rfl
  obtain ⟨σ, hσ, hσr⟩ := extraction_of_frequently_atTop hr
  -- iterate the key step through all phases
  have iter : ∀ j : ℕ, ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧ (∀ m, φ m % n = (r + j) % n) ∧
      Tendsto (fun m => x (φ m)) atTop (𝓝 p) := by
    intro j
    induction j with
    | zero =>
      refine ⟨ψ ∘ σ, (hψ.comp hσ).tendsto_atTop, fun m => ?_, hψlim.comp hσ.tendsto_atTop⟩
      have := congrArg Fin.val (hσr m)
      simp only [phase] at this
      simp only [Function.comp, add_zero, this, Nat.mod_eq_of_lt r.2]
    | succ j ih =>
      obtain ⟨φ, hφ, hφr, hφlim⟩ := ih
      refine ⟨fun m => φ m + 1, (tendsto_add_atTop_nat 1).comp hφ, fun m => ?_,
        (key φ hφ _ hφr hφlim).2⟩
      rw [Nat.add_mod, hφr m, ← Nat.add_mod, add_assoc]
  intro i
  obtain ⟨φ, hφ, hφr, hφlim⟩ := iter (i + n - r)
  have h := (key φ hφ _ hφr hφlim).1
  have hi : phase n ((r : ℕ) + (i + n - r)) = i := by
    ext
    simp only [phase]
    have : (r : ℕ) + (i + n - r) = i + n := by have := r.2; have := i.2; omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt i.2]
  rwa [hi] at h

end PotentialRepair
