import Mathlib

/-!
# Results derived in the walk through the layers (Section 5)

* Observer consensus (Section 5.1): finite descent, Newman's lemma (unique normal forms of a
  terminating, locally confluent repair relation), the cycle obstruction and the triangle over
  `ℤ/2`, and the noise bound `limsup ≤ ε / (1 - λ)`.
* Selection (Section 5.3): the replicator dynamics as `ẋ = M(x) ∇F`, the weighted-variance
  identity, positive semidefiniteness of `M(x)`, and the logarithmic balance law for averages.
-/

open Set Filter Topology MeasureTheory intervalIntegral

noncomputable section

namespace ObserverConsensus

/-! ### Finite descent -/

/-- **Finite descent.** If every accepted repair strictly lowers a potential that takes only
finitely many values, there is no infinite repair sequence. -/
theorem no_infinite_descent {S : Type*} (Φ : S → ℝ) (hfin : (Set.range Φ).Finite)
    (s : ℕ → S) : ¬ ∀ k, Φ (s (k + 1)) < Φ (s k) := by
  intro h
  have hanti : StrictAnti (fun k => Φ (s k)) := strictAnti_nat_of_succ_lt h
  have hinj : Function.Injective (fun k => Φ (s k)) := hanti.injective
  exact Set.infinite_range_of_injective hinj (hfin.subset (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩))

/-! ### Newman's lemma: unique normal forms -/

variable {α : Type*} (r : α → α → Prop)

/-- A state is a normal form when no repair step applies to it. -/
def IsNormal (a : α) : Prop := ∀ b, ¬ r a b

/-- Local confluence: two one-step repairs of the same state can be rejoined. -/
def LocallyConfluent : Prop :=
  ∀ a b c, r a b → r a c → ∃ d, Relation.ReflTransGen r b d ∧ Relation.ReflTransGen r c d

/-- Termination: there is no infinite repair sequence. -/
def Terminating : Prop := WellFounded (fun b a => r a b)

variable {r}

/-- **Newman's lemma.** A terminating, locally confluent relation is confluent. -/
theorem newman (ht : Terminating r) (hl : LocallyConfluent r) (a : α) :
    ∀ b c, Relation.ReflTransGen r a b → Relation.ReflTransGen r a c →
      ∃ d, Relation.ReflTransGen r b d ∧ Relation.ReflTransGen r c d := by
  induction a using ht.induction with
  | _ a ih =>
  intro b c hab hac
  rcases Relation.ReflTransGen.cases_head hab with rfl | ⟨b₁, hab₁, hb₁b⟩
  · exact ⟨c, hac, Relation.ReflTransGen.refl⟩
  rcases Relation.ReflTransGen.cases_head hac with rfl | ⟨c₁, hac₁, hc₁c⟩
  · exact ⟨b, Relation.ReflTransGen.refl, hab⟩
  obtain ⟨d₁, hb₁d₁, hc₁d₁⟩ := hl a b₁ c₁ hab₁ hac₁
  obtain ⟨e, hbe, hd₁e⟩ := ih b₁ hab₁ b d₁ hb₁b hb₁d₁
  obtain ⟨f, hcf, hef⟩ := ih c₁ hac₁ c e hc₁c (hc₁d₁.trans hd₁e)
  exact ⟨f, hbe.trans hef, hcf⟩

/-- Every state of a terminating repair relation reaches some normal form. -/
theorem exists_normal (ht : Terminating r) (a : α) :
    ∃ n, Relation.ReflTransGen r a n ∧ IsNormal r n := by
  induction a using ht.induction with
  | _ a ih =>
  by_cases h : IsNormal r a
  · exact ⟨a, Relation.ReflTransGen.refl, h⟩
  · simp only [IsNormal, not_forall, not_not] at h
    obtain ⟨b, hb⟩ := h
    obtain ⟨n, hbn, hn⟩ := ih b hb
    exact ⟨n, Relation.ReflTransGen.head hb hbn, hn⟩

/-- **Unique normal form.** A terminating, locally confluent repair relation gives each
initial state exactly one reachable normal form; hence every observable of the endpoint is
independent of the repair schedule. -/
theorem existsUnique_normal (ht : Terminating r) (hl : LocallyConfluent r) (a : α) :
    ∃! n, Relation.ReflTransGen r a n ∧ IsNormal r n := by
  obtain ⟨n, han, hn⟩ := exists_normal ht a
  refine ⟨n, ⟨han, hn⟩, ?_⟩
  rintro m ⟨ham, hm⟩
  obtain ⟨d, hnd, hmd⟩ := newman ht hl a n m han ham
  have h1 : n = d := by
    rcases Relation.ReflTransGen.cases_head hnd with h | ⟨e, he, _⟩
    · exact h
    · exact absurd he (hn e)
  have h2 : m = d := by
    rcases Relation.ReflTransGen.cases_head hmd with h | ⟨e, he, _⟩
    · exact h
    · exact absurd he (hm e)
  rw [h1, h2]

/-! ### Loops can forbid full agreement -/

/-- **Cycle obstruction (necessity).** If an assignment `x` satisfies abelian edge demands
`x (v (k+1)) - x (v k) = b k` around a closed cycle `v 0, …, v m = v 0`, the signed cycle sum
of the demands vanishes. -/
theorem cycle_sum_eq_zero {G V : Type*} [AddCommGroup G] (x : V → G) (v : ℕ → V) (b : ℕ → G)
    (m : ℕ) (hclosed : v m = v 0) (hdem : ∀ k < m, x (v (k + 1)) - x (v k) = b k) :
    ∑ k ∈ Finset.range m, b k = 0 := by
  have : ∑ k ∈ Finset.range m, b k = x (v m) - x (v 0) := by
    rw [← Finset.sum_range_sub (fun k => x (v k))]
    exact Finset.sum_congr rfl fun k hk => (hdem k (Finset.mem_range.mp hk)).symm
  rw [this, hclosed, sub_self]

/-- **The triangle over `ℤ/2` with demands `0, 0, 1`** has no global assignment. -/
theorem triangle_no_assignment :
    ¬ ∃ x : Fin 3 → ZMod 2, x 1 - x 0 = 0 ∧ x 2 - x 1 = 0 ∧ x 0 - x 2 = 1 := by
  decide

/-- Each edge of the triangle can be satisfied on its own. -/
theorem triangle_each_edge_satisfiable :
    (∃ x : Fin 3 → ZMod 2, x 1 - x 0 = 0) ∧ (∃ x : Fin 3 → ZMod 2, x 2 - x 1 = 0) ∧
      (∃ x : Fin 3 → ZMod 2, x 0 - x 2 = 1) := by
  decide

/-- Number of edges of the triangle whose demand is violated (unit weights). -/
def triangleMismatch (x : Fin 3 → ZMod 2) : ℕ :=
  (if x 1 - x 0 = 0 then 0 else 1) + (if x 2 - x 1 = 0 then 0 else 1) +
    (if x 0 - x 2 = 1 then 0 else 1)

/-- The minimum of the mismatch on the triangle is positive: every minimiser contains
irreducible residual inconsistency. -/
theorem triangle_mismatch_pos (x : Fin 3 → ZMod 2) : 0 < triangleMismatch x := by
  revert x; decide

/-! ### Noise -/

/-- **Noise bound.** If `a (m+1) ≤ λ a m + ε` with `0 ≤ λ < 1`, then
`a m ≤ λ^m a 0 + ε / (1 - λ)`. -/
theorem noise_bound_explicit {a : ℕ → ℝ} {lam ε : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (hε : 0 ≤ ε) (ha : ∀ m, a (m + 1) ≤ lam * a m + ε) (m : ℕ) :
    a m ≤ lam ^ m * a 0 + ε / (1 - lam) := by
  have h1 : 0 < 1 - lam := by linarith
  induction m with
  | zero => simp; positivity
  | succ m ih =>
    calc a (m + 1) ≤ lam * a m + ε := ha m
      _ ≤ lam * (lam ^ m * a 0 + ε / (1 - lam)) + ε := by gcongr
      _ = lam ^ (m + 1) * a 0 + ε / (1 - lam) := by field_simp; ring

/-- **Noise bound (`limsup a ≤ ε / (1 - λ)`).** If `a (m+1) ≤ λ a m + ε` with `0 ≤ λ < 1`
and `ε ≥ 0`, then for every `δ > 0`, eventually `a m ≤ ε / (1 - λ) + δ`. -/
theorem noise_bound {a : ℕ → ℝ} {lam ε : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam < 1) (hε : 0 ≤ ε)
    (ha : ∀ m, a (m + 1) ≤ lam * a m + ε) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m in atTop, a m ≤ ε / (1 - lam) + δ := by
  have hlim : Tendsto (fun m => lam ^ m * a 0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hl0 hl1).mul_const (a 0)
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with m hm
  have := noise_bound_explicit hl0 hl1 hε ha m
  linarith

end ObserverConsensus

namespace Selection

open Matrix

variable {ι : Type*} [Fintype ι]

/-- Fitness `fᵢ(x) = (A x)ᵢ`. -/
def fitness (A : Matrix ι ι ℝ) (x : ι → ℝ) : ι → ℝ := A *ᵥ x

/-- Mean fitness `f̄(x) = ∑ⱼ xⱼ fⱼ(x)`. -/
def meanFitness (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := ∑ j, x j * fitness A x j

/-- The replicator vector field `xᵢ (fᵢ(x) - f̄(x))`. -/
def replicator (A : Matrix ι ι ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => x i * (fitness A x i - meanFitness A x)

/-- The mobility `M(x) = diag(x) - x xᵀ`. -/
def mobility [DecidableEq ι] (x : ι → ℝ) : Matrix ι ι ℝ := diagonal x - vecMulVec x x

/-- **The shared equation.** The replicator field is `M(x) ∇F` with `∇F = A x`. -/
theorem replicator_eq_mobility [DecidableEq ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    replicator A x = mobility x *ᵥ fitness A x := by
  funext i
  simp only [replicator, mobility, sub_mulVec, Pi.sub_apply, mulVec_diagonal, meanFitness]
  simp only [mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum]
  ring

/-- For symmetric `A`, `∇F = A x`, where `F(x) = ½ xᵀ A x`. -/
theorem potential_directional_deriv (A : Matrix ι ι ℝ) (hA : Aᵀ = A) (x v : ι → ℝ) :
    HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * ((x + t • v) ⬝ᵥ (A *ᵥ (x + t • v))))
      (v ⬝ᵥ fitness A x) 0 := by
  have hsymm : v ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ v) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]
  have hpoly : (fun t : ℝ => (1 / 2 : ℝ) * ((x + t • v) ⬝ᵥ (A *ᵥ (x + t • v)))) =
      fun t => (1 / 2 : ℝ) * (x ⬝ᵥ (A *ᵥ x)) + t * (v ⬝ᵥ (A *ᵥ x)) +
        t ^ 2 * ((1 / 2 : ℝ) * (v ⬝ᵥ (A *ᵥ v))) := by
    funext t
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    rw [← hsymm]
    ring
  rw [hpoly]
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const (v ⬝ᵥ (A *ᵥ x))).const_add
    ((1 / 2 : ℝ) * (x ⬝ᵥ (A *ᵥ x)))
  have h2 := ((hasDerivAt_pow 2 (0 : ℝ)).mul_const ((1 / 2 : ℝ) * (v ⬝ᵥ (A *ᵥ v))))
  convert h.add h2 using 1
  · simp [fitness]

/-- `M(x) v = (xᵢ vᵢ - xᵢ (x · v))ᵢ`. -/
theorem mobility_mulVec [DecidableEq ι] (x v : ι → ℝ) :
    mobility x *ᵥ v = fun i => x i * v i - x i * (x ⬝ᵥ v) := by
  funext i
  rw [mobility, sub_mulVec, Pi.sub_apply, mulVec_diagonal]
  simp only [mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum]

/-- `M(x) 1 = 0` on the simplex: the mobility preserves total frequency. -/
theorem mobility_one [DecidableEq ι] {x : ι → ℝ} (hx : ∑ i, x i = 1) :
    mobility x *ᵥ (fun _ => 1) = 0 := by
  rw [mobility_mulVec]
  funext i
  simp [dotProduct, hx]

/-- **Weighted-variance identity.** On the simplex, `vᵀ M(x) v = ∑ᵢ xᵢ (vᵢ - x·v)²`. -/
theorem quadratic_mobility [DecidableEq ι] {x : ι → ℝ} (hx : ∑ i, x i = 1) (v : ι → ℝ) :
    v ⬝ᵥ (mobility x *ᵥ v) = ∑ i, x i * (v i - x ⬝ᵥ v) ^ 2 := by
  rw [mobility_mulVec]
  set m := x ⬝ᵥ v with hm
  have hm' : m = ∑ i, x i * v i := rfl
  calc v ⬝ᵥ (fun i => x i * v i - x i * m)
      = ∑ i, x i * v i ^ 2 - m * ∑ i, x i * v i := by
        simp only [dotProduct, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, (x i * v i ^ 2 - 2 * m * (x i * v i) + m ^ 2 * x i) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          hx, ← hm']
        ring
    _ = ∑ i, x i * (v i - m) ^ 2 := Finset.sum_congr rfl fun i _ => by ring

/-- `M(x)` is positive semidefinite on the simplex. -/
theorem mobility_psd [DecidableEq ι] {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx : ∑ i, x i = 1)
    (v : ι → ℝ) : 0 ≤ v ⬝ᵥ (mobility x *ᵥ v) := by
  rw [quadratic_mobility hx]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hx0 i) (sq_nonneg _)

/-- **Mean fitness climbs.** Along the replicator dynamics with symmetric payoffs, the rate of
change of `F = ½ xᵀ A x` is `∇Fᵀ ẋ = ∑ᵢ xᵢ (fᵢ - f̄)² ≥ 0`. -/
theorem potential_rate [DecidableEq ι] (A : Matrix ι ι ℝ) {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hx : ∑ i, x i = 1) :
    fitness A x ⬝ᵥ replicator A x = ∑ i, x i * (fitness A x i - meanFitness A x) ^ 2 ∧
      0 ≤ fitness A x ⬝ᵥ replicator A x := by
  have h : fitness A x ⬝ᵥ replicator A x =
      ∑ i, x i * (fitness A x i - meanFitness A x) ^ 2 := by
    rw [replicator_eq_mobility, quadratic_mobility hx]
    rfl
  refine ⟨h, ?_⟩
  rw [h]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hx0 i) (sq_nonneg _)

/-- A state of the simplex at which all present types earn the same is a rest point; in
particular if all `(A p)ᵢ` are equal, `p` is a rest point of the replicator dynamics. -/
theorem rest_of_equal_fitness (A : Matrix ι ι ℝ) {p : ι → ℝ} (hp : ∑ i, p i = 1) {c : ℝ}
    (hc : ∀ i, fitness A p i = c) : replicator A p = 0 := by
  have hmean : meanFitness A p = c := by
    simp only [meanFitness, hc, ← Finset.sum_mul, hp, one_mul]
  funext i
  simp [replicator, hc, hmean]

/-- **A population that cycles agrees on average.** If every type stays positive along the
replicator dynamics on `[0, T]`, then
`(log xᵢ(T) - log xᵢ(0)) / T = (A x̄_T)ᵢ - (1/T) ∫₀ᵀ f̄(x(t)) dt`. -/
theorem log_balance (A : Matrix ι ι ℝ) {x : ℝ → ι → ℝ} {T : ℝ} (hT : 0 < T)
    (hpos : ∀ i, ∀ t ∈ Icc 0 T, 0 < x t i)
    (hx : ∀ i, ∀ t ∈ Icc 0 T, HasDerivAt (fun t => x t i) (replicator A (x t) i) t) (i : ι) :
    (Real.log (x T i) - Real.log (x 0 i)) / T =
      fitness A (fun j => T⁻¹ * ∫ t in (0 : ℝ)..T, x t j) i -
        T⁻¹ * ∫ t in (0 : ℝ)..T, meanFitness A (x t) := by
  have hxc : ∀ j, ContinuousOn (fun t => x t j) (Icc 0 T) := fun j t ht =>
    (hx j t ht).continuousAt.continuousWithinAt
  have hxi : ∀ j, IntervalIntegrable (fun t => x t j) volume 0 T := fun j =>
    ((hxc j).mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
  have hfc : ContinuousOn (fun t => fitness A (x t) i) (Icc 0 T) := by
    simp only [fitness, mulVec, dotProduct]
    exact continuousOn_finset_sum _ fun j _ => continuousOn_const.mul (hxc j)
  have hmc : ContinuousOn (fun t => meanFitness A (x t)) (Icc 0 T) := by
    simp only [meanFitness, fitness, mulVec, dotProduct]
    exact continuousOn_finset_sum _ fun j _ =>
      (hxc j).mul (continuousOn_finset_sum _ fun k _ => continuousOn_const.mul (hxc k))
  have hfi : IntervalIntegrable (fun t => fitness A (x t) i) volume 0 T :=
    (hfc.mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
  have hmi : IntervalIntegrable (fun t => meanFitness A (x t)) volume 0 T :=
    (hmc.mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
  -- `d/dt log xᵢ = fᵢ - f̄`
  have hlog : ∀ t ∈ uIcc 0 T, HasDerivAt (fun t => Real.log (x t i))
      (fitness A (x t) i - meanFitness A (x t)) t := by
    intro t ht
    rw [uIcc_of_le hT.le] at ht
    have h := (hx i t ht).log (hpos i t ht).ne'
    convert h using 1
    simp only [replicator]
    field_simp [(hpos i t ht).ne']
  have hftc := integral_eq_sub_of_hasDerivAt hlog (hfi.sub hmi)
  rw [intervalIntegral.integral_sub hfi hmi] at hftc
  -- the integral of the fitness is the fitness of the integral
  have hlin : ∫ t in (0 : ℝ)..T, fitness A (x t) i =
      T * fitness A (fun j => T⁻¹ * ∫ t in (0 : ℝ)..T, x t j) i := by
    simp only [fitness, mulVec, dotProduct]
    rw [intervalIntegral.integral_finset_sum fun j _ => (hxi j).const_mul _]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul]
    field_simp
  rw [← hftc, hlin]
  field_simp

/-- **Every limit point of the time averages is a rest point.** Along the replicator
dynamics on the simplex, if every type stays bounded away from zero (`m ≤ xᵢ(t)`), then every
limit point `p` of the time averages `x̄_T` lies in the simplex and equalises fitness, hence
is a rest point of the replicator dynamics. -/
theorem time_average_limit_rest [DecidableEq ι] (A : Matrix ι ι ℝ) {x : ℝ → ι → ℝ} {m : ℝ}
    (hm : 0 < m) (hlow : ∀ t, 0 ≤ t → ∀ i, m ≤ x t i) (hsum : ∀ t, 0 ≤ t → ∑ i, x t i = 1)
    (hx : ∀ i, ∀ t, 0 ≤ t → HasDerivAt (fun t => x t i) (replicator A (x t) i) t)
    {p : ι → ℝ}
    (hp : MapClusterPt p atTop (fun T : ℝ => fun j => T⁻¹ * ∫ t in (0 : ℝ)..T, x t j)) :
    (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ replicator A p = 0 := by
  set xbar : ℝ → ι → ℝ := fun T j => T⁻¹ * ∫ t in (0 : ℝ)..T, x t j
  have hxc : ∀ T, ∀ j, ContinuousOn (fun t => x t j) (Icc 0 T) := fun T j t ht =>
    (hx j t ht.1).continuousAt.continuousWithinAt
  have hxi : ∀ T, 0 < T → ∀ j, IntervalIntegrable (fun t => x t j) volume 0 T := fun T hT j =>
    ((hxc T j).mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
  have hup : ∀ t, 0 ≤ t → ∀ i, x t i ≤ 1 := by
    intro t ht i
    rw [← hsum t ht]
    exact Finset.single_le_sum (fun j _ => hm.le.trans (hlow t ht j)) (Finset.mem_univ i)
  -- the averages lie in the simplex
  have hbar_nonneg : ∀ T, 0 < T → ∀ j, 0 ≤ xbar T j := by
    intro T hT j
    refine mul_nonneg (inv_nonneg.mpr hT.le) (intervalIntegral.integral_nonneg hT.le ?_)
    intro t ht; exact hm.le.trans (hlow t ht.1 j)
  have hbar_sum : ∀ T, 0 < T → ∑ j, xbar T j = 1 := by
    intro T hT
    simp only [xbar, ← Finset.mul_sum]
    rw [← intervalIntegral.integral_finset_sum fun j _ => hxi T hT j]
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) fun t ht => by
      rw [uIcc_of_le hT.le] at ht; exact hsum t ht.1]
    simp [hT.ne']
  have hS : IsClosed {y : ι → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} := by
    rw [Set.setOf_and, Set.setOf_forall]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const)
  have hev : ∀ᶠ T in atTop, xbar T ∈ {y : ι → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    exact ⟨hbar_nonneg T hT, hbar_sum T hT⟩
  have hpS := hS.closure_eq ▸ clusterPt_iff_forall_mem_closure.mp hp _ hev
  obtain ⟨hp0, hp1⟩ := hpS
  refine ⟨hp0, hp1, ?_⟩
  -- fitness differences of the averages tend to zero
  have hlog : ∀ t, 0 ≤ t → ∀ i, |Real.log (x t i)| ≤ -Real.log m := by
    intro t ht i
    have h1 : Real.log m ≤ Real.log (x t i) := Real.log_le_log hm (hlow t ht i)
    have h2 : Real.log (x t i) ≤ 0 := Real.log_nonpos (hm.le.trans (hlow t ht i)) (hup t ht i)
    rw [abs_le]; constructor <;> linarith
  have hdiff : ∀ i j, Tendsto (fun T => fitness A (xbar T) i - fitness A (xbar T) j) atTop
      (𝓝 0) := by
    intro i j
    have hb : Tendsto (fun T : ℝ => 4 * -Real.log m / T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hpos : ∀ k, ∀ t ∈ Icc 0 T, 0 < x t k := fun k t ht => hm.trans_le (hlow t ht.1 k)
    have hi := log_balance A hT hpos (fun k t ht => hx k t ht.1) i
    have hj := log_balance A hT hpos (fun k t ht => hx k t ht.1) j
    have e : fitness A (xbar T) i - fitness A (xbar T) j =
        (Real.log (x T i) - Real.log (x 0 i)) / T - (Real.log (x T j) - Real.log (x 0 j)) / T := by
      rw [hi, hj]; ring
    rw [e, Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hT]
    gcongr
    have := hlog T hT.le i; have := hlog 0 le_rfl i
    have := hlog T hT.le j; have := hlog 0 le_rfl j
    rw [abs_le] at *
    constructor <;> linarith
  -- pass to the limit point
  have hfc : ∀ i, Continuous fun y : ι → ℝ => fitness A y i := fun i => by
    simp only [fitness, mulVec, dotProduct]
    exact continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_apply j)
  have heq : ∀ i j, fitness A p i = fitness A p j := by
    intro i j
    have hc : Continuous fun y : ι → ℝ => fitness A y i - fitness A y j := (hfc i).sub (hfc j)
    have hcl : MapClusterPt (fitness A p i - fitness A p j) atTop
        (fun T => fitness A (xbar T) i - fitness A (xbar T) j) :=
      hp.tendsto_comp (hc.tendsto p)
    have : fitness A p i - fitness A p j = 0 := eq_of_nhds_neBot (ClusterPt.mono hcl (hdiff i j))
    linarith
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    exact rest_of_equal_fitness A hp1 (c := fitness A p i₀) fun i => heq i i₀
  · funext i; exact absurd ⟨i⟩ hι

end Selection
