import Mathlib

/-!
# Repair networks (Section 2)

Definitions 1–3 of the paper, together with surprise and detuning.

The state of node `i` lives in `EuclideanSpace ℝ (Fin (d i))`; the global state is the
product, carrying the sup norm of the product (any norm is equivalent in finite dimension;
the abstract theorems in the other files are stated for arbitrary normed spaces).
-/

open Set

noncomputable section

namespace RepairNetwork

/-- Space in which node `i` holds its state. -/
abbrev NodeSpace {V : Type*} (d : V → ℕ) (i : V) := EuclideanSpace ℝ (Fin (d i))

/-- Global state: one vector per node. -/
abbrev State {V : Type*} (d : V → ℕ) := ∀ i, NodeSpace d i

end RepairNetwork

open RepairNetwork

/-- **Definition 1 (Repair network).** A finite set of nodes `V`; for each node `i` a state
space `X i ⊆ ℝ^{d i}`, a neighbourhood `N i ⊆ V`, a set of evidence `Ev i`, and a repair map
`R i` which reads only the states of the neighbours and the node's own evidence, and returns a
value in `X i` whenever the neighbours hold values in their own state spaces. -/
structure RepairNet (V : Type*) [Fintype V] (d : V → ℕ) where
  /-- state space of each node -/
  X : ∀ i, Set (NodeSpace d i)
  /-- neighbourhood of each node -/
  N : V → Set V
  /-- evidence that can be imposed on each node -/
  Ev : V → Type*
  /-- the repair map of each node -/
  R : ∀ i, (∀ j : N i, NodeSpace d j) → Ev i → NodeSpace d i
  /-- the repair map takes values in the node's state space -/
  mapsTo : ∀ i (y : ∀ j : N i, NodeSpace d j) (e : Ev i), (∀ j : N i, y j ∈ X j) → R i y e ∈ X i

namespace RepairNet

variable {V : Type*} [Fintype V] {d : V → ℕ} (net : RepairNet V d)

/-- The global state space `X = ∏ X i`. -/
def space : Set (State d) := Set.pi univ net.X

/-- Global evidence `E = ∏ E i`. -/
def Evidence := ∀ i, net.Ev i

/-- The global repair map `R(x, e) = (R i (x_{N(i)}, e i))_i`. -/
def globalR (x : State d) (e : net.Evidence) : State d :=
  fun i => net.R i (fun j => x j) (e i)

/-- Locality: the repair target of node `i` depends only on the neighbours of `i`. -/
theorem globalR_local (x y : State d) (e : net.Evidence) (i : V)
    (h : ∀ j ∈ net.N i, x j = y j) : net.globalR x e i = net.globalR y e i := by
  unfold globalR
  congr 1
  funext j
  exact h j j.2

theorem globalR_mapsTo (e : net.Evidence) : MapsTo (fun x => net.globalR x e) net.space net.space := by
  intro x hx i _
  exact net.mapsTo i _ _ (fun j => hx j (mem_univ _))

/-- **Definition 2.** Disagreement of node `i`: `δᵢ(x,e) = ‖Rᵢ(x_{N(i)}, eᵢ) - xᵢ‖`. -/
def nodeDisagreement (x : State d) (e : net.Evidence) (i : V) : ℝ :=
  ‖net.globalR x e i - x i‖

/-- **Definition 2.** Disagreement of the network: `D(x,e) = ‖R(x,e) - x‖`. -/
def disagreement (x : State d) (e : net.Evidence) : ℝ :=
  ‖net.globalR x e - x‖

/-- **Definition 2.** An equilibrium under `e` is a state in `X` at which no node disagrees:
`x⋆ = R(x⋆, e)`. -/
def IsEquilibrium (x : State d) (e : net.Evidence) : Prop :=
  x ∈ net.space ∧ net.globalR x e = x

theorem isEquilibrium_iff_nodeDisagreement (x : State d) (e : net.Evidence) :
    net.IsEquilibrium x e ↔ x ∈ net.space ∧ ∀ i, net.nodeDisagreement x e i = 0 := by
  unfold IsEquilibrium nodeDisagreement
  simp only [norm_eq_zero, sub_eq_zero]
  exact and_congr_right fun _ => funext_iff

theorem isEquilibrium_iff_disagreement (x : State d) (e : net.Evidence) :
    net.IsEquilibrium x e ↔ x ∈ net.space ∧ net.disagreement x e = 0 := by
  unfold IsEquilibrium disagreement
  simp [sub_eq_zero]

/-- **Surprise.** A change of evidence `e → e'` under which the equilibrium `x` under `e`
stops being one. -/
def IsSurprise (x : State d) (e e' : net.Evidence) : Prop :=
  net.IsEquilibrium x e ∧ 0 < net.disagreement x e'

/-- **Detuning.** The disagreement that evidence `e` creates at a reference rest `x₀`
(an equilibrium under the reference evidence): `Δ(e) = ‖R(x₀, e) - x₀‖`. -/
def detuning (x₀ : State d) (e : net.Evidence) : ℝ := net.disagreement x₀ e

end RepairNet

/-! ### Definition 3 (repair processes), stated for an arbitrary self-map `R` of a vector
space; for a network take `R = fun x => net.globalR x e`. -/

namespace Repair

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- One damped repair step `x ↦ x + η (R x - x)`; `η = 1` is synchronous repair. -/
def dampedStep (R : E → E) (η : ℝ) (x : E) : E := x + η • (R x - x)

/-- The damped repair sequence `x_{t+1} = x_t + η (R(x_t) - x_t)`. -/
def damped (R : E → E) (η : ℝ) (x₀ : E) : ℕ → E
  | 0 => x₀
  | t + 1 => dampedStep R η (damped R η x₀ t)

/-- Synchronous repair `x_{t+1} = R(x_t)`. -/
def synchronous (R : E → E) (x₀ : E) : ℕ → E := fun t => R^[t] x₀

theorem damped_one (R : E → E) (x₀ : E) : damped R 1 x₀ = synchronous R x₀ := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [damped, ih, synchronous, dampedStep, one_smul, add_sub_cancel,
      Function.iterate_succ_apply']

/-- The rest points of damped repair (`η ≠ 0`) are exactly the equilibria. -/
theorem dampedStep_fixed_iff (R : E → E) {η : ℝ} (hη : η ≠ 0) (x : E) :
    dampedStep R η x = x ↔ R x = x := by
  unfold dampedStep
  constructor
  · intro h
    have : η • (R x - x) = 0 := by simpa using h
    rcases smul_eq_zero.mp this with h | h
    · exact absurd h hη
    · exact sub_eq_zero.mp h
  · intro h; simp [h]

/-- Damped repair stays in a convex domain that `R` maps into itself. -/
theorem dampedStep_mem {R : E → E} {X : Set E} (hX : Convex ℝ X) (hR : MapsTo R X X)
    {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) {x : E} (hx : x ∈ X) : dampedStep R η x ∈ X := by
  have : dampedStep R η x = (1 - η) • x + η • R x := by
    unfold dampedStep; rw [smul_sub, sub_smul, one_smul]; abel
  rw [this]
  exact hX hx (hR hx) (by linarith) h0 (by ring)

theorem damped_mem {R : E → E} {X : Set E} (hX : Convex ℝ X) (hR : MapsTo R X X)
    {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) {x₀ : E} (hx : x₀ ∈ X) (t : ℕ) : damped R η x₀ t ∈ X := by
  induction t with
  | zero => exact hx
  | succ t ih => exact dampedStep_mem hX hR h0 h1 ih

end Repair
