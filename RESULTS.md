# Formal derivation of the results of "Agreement and Surprise"

All files build with `lake build`; there is no `sorry`, and the main results depend only on
the standard axioms `propext`, `Classical.choice`, `Quot.sound` (checked by the `#print axioms`
lines at the end of `RequestProject/Main.lean`).

| Paper | Lean | File |
|---|---|---|
| Def. 1–3, surprise, detuning | `RepairNet`, `RepairNet.globalR`, `nodeDisagreement`, `disagreement`, `IsEquilibrium`, `IsSurprise`, `detuning`, `Repair.damped`, `Repair.synchronous` | `Defs.lean` |
| Rest points of damped repair = equilibria; damped repair stays in a convex domain | `Repair.dampedStep_fixed_iff`, `Repair.damped_mem` | `Defs.lean` |
| **Theorem 4** (existence) | `RepairNet.exists_equilibrium` | `Existence.lean` |
| Brouwer's fixed-point theorem (needed for Thm 4; not in Mathlib, proved here) | `brouwer_fixed_point` | `Brouwer/*.lean` |
| **Theorem 5** (1) unique equilibrium | `Repair.contraction_existsUnique_fixedPoint`, `RepairNet.existsUnique_equilibrium_of_contraction` | `Contraction.lean` |
| Theorem 5 (2) damped/synchronous rate `(1-η+ηq)^t` | `Repair.damped_dist_le`, `Repair.damped_tendsto`, `Repair.damped_one` | `Contraction.lean` |
| Theorem 5 (3) relaxation rate `e^{-(1-q)t}` | `Repair.relaxation_dist_le` | `Contraction.lean` |
| Theorem 5 (4) sensitivity `L‖e-e'‖/(1-q)` | `Repair.fixedPoint_lipschitz_evidence` | `Contraction.lean` |
| **Theorem 6** (potential) | `PotentialRepair.cyclic_antitone`, `PotentialRepair.limit_point_is_equilibrium` | `Potential.lean` |
| **Proposition 7** (two-node loop) | `TwoNodeLoop.hypotheses_existence`, `fixed_iff`, `synchronous_not_tendsto`, `relaxation_not_tendsto`, `relaxation_stays_in_square` | `TwoNodeLoop.lean` |
| **Proposition 8** and the damped identity | `Repair.agreement_on_average`, `Repair.damped_average_identity`, `Repair.damped_average_bound` | `Averages.lean` |
| **Corollary 9** | `Repair.linear_repair_limit_points` | `Averages.lean` |
| **Corollary 10** and the Lipschitz closure gap | `RateLaw.rate_law`, `Repair.lipschitz_closure_gap` | `Averages.lean` |
| **Proposition 11** | `ChargeBalance.charge_balance` | `Averages.lean` |
| **Theorem 12** and detuning bound | `Repair.displacement_bounds`, `RepairNet.equilibrium_displacement`, `Repair.detuning_zero_iff` | `Contraction.lean` |
| **Theorem 13** (equilibrium propagation) | `EqProp.two_equilibria_give_gradient` | `EqProp.lean` |
| Pairwise energy, two speeds, no surprise ⇒ no learning | `EqProp.pairwise_energy_partial`, `EqProp.two_speed_dissipation`, `EqProp.free_state_stationary_nudged`, `EqProp.no_surprise_no_learning` | `EqProp.lean` |
| §5.1 finite descent, Newman/unique normal forms, cycle obstruction, triangle over ℤ/2, noise bound | `ObserverConsensus.*` | `Layers.lean` |
| §5.3 replicator = `M(x)∇F`, variance identity, `Ḟ ≥ 0`, log balance, limit points of averages are rest points | `Selection.*` | `Layers.lean` |

## Modelling choices and what is not covered

* Theorem 5 (3): the relaxation trajectory is assumed to stay in `X`.
* Proposition 8 / Corollary 10: the repair map (resp. signals) is assumed continuous so that the
  time averages are integrals.
* Proposition 11 is stated for the integrated (distributional) form of the spiking equations
  over the window.
* Proposition 7: the claim that every relaxation trajectory converges to a periodic orbit
  needs the Poincaré–Bendixson theorem, which is not in Mathlib, so it is not formalized.
  What is proved: the equilibrium is unique, trajectories stay in the square, and no
  synchronous or relaxation trajectory starting elsewhere converges.
* Results that the paper cites rather than proves (asynchronous convergence, Kakutani,
  Nash, Arrow–Debreu, Aumann, DeGroot, sheaf heat flow, the OPH reconstruction results) are not
  formalized, and neither are the numerical simulations of Section 6.
