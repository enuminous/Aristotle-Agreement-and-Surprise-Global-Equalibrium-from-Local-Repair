import RequestProject.Defs
import RequestProject.Brouwer.Convex

/-!
# An equilibrium exists (Theorem 4)
-/

open Set

namespace RepairNet

variable {V : Type*} [Fintype V] {d : V → ℕ} (net : RepairNet V d)

/-- **Theorem 4 (Existence).** If every node's state space is nonempty, compact and convex,
and the global repair map `R(·, e)` is continuous on `X`, the network has an equilibrium
under `e`. -/
theorem exists_equilibrium (e : net.Evidence) (hne : ∀ i, (net.X i).Nonempty)
    (hcpt : ∀ i, IsCompact (net.X i)) (hcvx : ∀ i, Convex ℝ (net.X i))
    (hcont : ContinuousOn (fun x => net.globalR x e) net.space) :
    ∃ x, net.IsEquilibrium x e := by
  obtain ⟨x, hx, hfix⟩ := brouwer_fixed_point (isCompact_univ_pi hcpt)
    (convex_pi fun i _ => hcvx i) (Set.univ_pi_nonempty_iff.mpr hne) hcont
    (net.globalR_mapsTo e)
  exact ⟨x, hx, hfix⟩

end RepairNet
