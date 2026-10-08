# Summary of changes for run 9cf083ab-5270-4f61-9c03-a2ccf1cd5d6e
I read your one-word request ("Derive") as: formalize and prove in Lean the formal results of the attached paper, "Agreement and Surprise: Global Equilibrium from Local Repair". The project builds (`lake build`) with no `sorry`. The axiom checks at the end of `RequestProject/Main.lean` show only the standard `propext`, `Classical.choice` and `Quot.sound`. `RESULTS.md` maps each paper statement to its Lean name and lists the caveats.

**What is proved, by file (all under `RequestProject/`):**
- `Defs.lean`: Definitions 1–3. These cover repair networks, the global repair map, disagreement, equilibrium, surprise and detuning, plus the damped and synchronous repair processes.
- `Existence.lean`: Theorem 4, existence of an equilibrium.
  - Mathlib has no Brouwer fixed-point theorem, so I proved it from scratch in `Brouwer/` (`DetPoly`, `NoRetraction`, `Ball`, `Convex`).
  - The route is: no smooth retraction of the ball onto its boundary (a polynomial Jacobian-integral argument), then smoothing, then extension to convex sets by nearest-point projection.
- `Contraction.lean`: Theorem 5, items 1–4, and Theorem 12 (displacement bounds), with versions stated for networks.
- `Potential.lean`: Theorem 6.
- `TwoNodeLoop.lean`: Proposition 7. It covers:
  - the unique equilibrium;
  - non-convergence of synchronous repair and of relaxation;
  - the square being invariant.
- `Averages.lean`: Proposition 8 and the damped identity, Corollary 9, Corollary 10 (rate law), the Lipschitz closure gap, and Proposition 11 (charge balance).
- `EqProp.lean`: Theorem 13 and related results.
- `Layers.lean`: the derivations in Section 5.
  - Section 5.1, consensus: Newman's lemma, the triangle example with no consistent assignment, and the noise bound.
  - Section 5.3, selection: the time-average limit results.

**Caveats:**
- **Proposition 7:** the periodic-orbit claim is not formalized. Proving it needs the Poincaré–Bendixson theorem, which is not in Mathlib.
- **Theorem 5(3):** stated with the extra assumption that the trajectory stays in `X`.
- **Proposition 8 and Corollary 10:** assume continuity of the relevant functions.
- **Proposition 11:** stated in integrated form.
- **Not formalized at all:** results the paper only cites from other sources, and the Section 6 simulations.