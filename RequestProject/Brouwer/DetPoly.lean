import Mathlib

/-!
# `t ↦ det (id + t • A)` is a polynomial of degree at most `dim E`

We express it through Lagrange interpolation at the nodes `0, 1, …, dim E`, which makes the
polynomial dependence on `t` uniform in `A` and lets us integrate over `A`.
-/

open Polynomial Finset

noncomputable section

namespace BrouwerAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The interpolation nodes `0, 1, …, dim E`. -/
abbrev nodes (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Finset ℕ :=
  range (Module.finrank ℝ E + 1)

/-- The Lagrange basis polynomial at node `j`. -/
abbrev lag (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ) : ℝ[X] :=
  Lagrange.basis (nodes E) (fun k : ℕ => (k : ℝ)) j

/-- `det (id + t • A)` is the value at `t` of a polynomial of degree at most `dim E`. -/
theorem exists_poly_det (A : E →L[ℝ] E) :
    ∃ p : ℝ[X], p.natDegree ≤ Module.finrank ℝ E ∧
      ∀ t : ℝ, eval t p = (ContinuousLinearMap.id ℝ E + t • A).det := by
  set b := Module.finBasis ℝ E
  set M := LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)
  refine ⟨Matrix.det ((X : ℝ[X]) • M.map C + (1 : Matrix (Fin _) (Fin _) ℝ).map C), ?_, ?_⟩
  · have := natDegree_det_X_add_C_le M (1 : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ)
    simpa using this
  · intro t
    have h1 : eval t (Matrix.det ((X : ℝ[X]) • M.map C + (1 : Matrix _ _ ℝ).map C)) =
        Matrix.det (t • M + 1) := by
      rw [← coe_evalRingHom, RingHom.map_det]
      congr 1
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> simp [mul_comm]
    rw [h1, ContinuousLinearMap.det, ← LinearMap.det_toMatrix b]
    congr 1
    simp [M, map_add, map_smul, add_comm]

/-- **Lagrange form.** For every `t`,
`det (id + t • A) = ∑_{j ∈ nodes} det (id + j • A) · ℓⱼ(t)`. -/
theorem det_add_smul_eq_sum (A : E →L[ℝ] E) (t : ℝ) :
    (ContinuousLinearMap.id ℝ E + t • A).det =
      ∑ j ∈ nodes E, (ContinuousLinearMap.id ℝ E + (j : ℝ) • A).det * eval t (lag E j) := by
  obtain ⟨p, hdeg, hp⟩ := exists_poly_det A
  have hinj : Set.InjOn (fun k : ℕ => (k : ℝ)) (nodes E) := fun a _ b _ h => by
    simpa using h
  have hlt : p.degree < #(nodes E) := by
    rw [card_range]
    calc p.degree ≤ p.natDegree := degree_le_natDegree
      _ < (Module.finrank ℝ E + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_of_le hdeg
  have := Lagrange.eq_interpolate hinj hlt
  rw [← hp, this, Lagrange.interpolate_apply, eval_finset_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, hp]

end BrouwerAux
