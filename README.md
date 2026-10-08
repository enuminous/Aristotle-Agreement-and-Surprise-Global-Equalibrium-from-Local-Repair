# Agreement and Surprise

## Global Equilibrium from Local Repair — Aristotle / Lean 4 formalization

An independent formalization of results from **Bernhard Mueller's _Agreement and Surprise: Global Equilibrium from Local Repair_**, draft dated 6 October 2026. The paper studies networks whose parts correct their states using local information, and asks when agreement exists, when repair reaches it, and what remains true when states keep moving.

This repository contains the 26-page paper, Lean source produced with **Aristotle (Harmonic)**, a statement-to-proof map, and a self-contained research landing page. Maintained by **Matthew Chenoweth Wright (@enuminous)**.

[Read the paper](22ACBA52-C160-11F1-BAAE-D7B44D786CDB.pdf) · [Results and theorem map](RESULTS.md) · [Aristotle's report](ARISTOTLE_SUMMARY.md) · [Landing-page source](index.html)

## At a glance

| Item | Repository snapshot |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.28.0` |
| Mathlib | `v4.28.0`, resolved to `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |
| Lean source | 13 files, including four Brouwer-support modules |
| Explicit `theorem` declarations | 95, including supporting lemmas; this is not a count of new paper results |
| Axiom-check entry point | 10 `#print axioms` commands in [`RequestProject/Main.lean`](RequestProject/Main.lean) |
| Imported build report | `lake build` succeeds, no `sorry`, and the checked main results use only `propext`, `Classical.choice`, `Quot.sound` |

The build and axiom claims above are reported in [`ARISTOTLE_SUMMARY.md`](ARISTOTLE_SUMMARY.md) and [`RESULTS.md`](RESULTS.md). Source inspection for this documentation found no `sorry` or `admit` tokens in the Lean files. **A fresh Lean build was not run for this documentation update.** The source inventory refers to commit [`ea54c6e`](https://github.com/enuminous/Aristotle-Agreement-and-Surprise-Global-Equalibrium-from-Local-Repair/tree/ea54c6e78ae8af0d27bc84675dc37d77100a51c7).

## The mathematical mechanism

Each node has a state, a neighbourhood, an evidence input and a repair map. The assembled map is $R(x,e)$, and disagreement is

$$
D(x,e)=\|R(x,e)-x\|.
$$

An equilibrium lies in the allowed state space and satisfies $R(x^*,e)=x^*$. Damped repair takes the form

$$
x_{t+1}=x_t+\eta\bigl(R(x_t,e)-x_t\bigr).
$$

For $\eta=1$ this is synchronous repair. Continuous relaxation is $\dot x=R(x,e)-x$. Agreement means that each node satisfies its own repair equation; different nodes can hold different values.

The central distinctions are **existence, reachability, uniqueness and agreement on average**. They require different assumptions. An equilibrium may exist even when repair from other states never converges to it.

## Navigate the formalization

| Paper result | What the formalization covers | Lean source |
| --- | --- | --- |
| Definitions 1–3 | Repair networks, locality, disagreement, equilibrium, surprise, detuning and repair processes | [Defs.lean](RequestProject/Defs.lean) |
| Theorem 4 | Existence on nonempty compact convex node domains with a continuous global repair map | [Existence.lean](RequestProject/Existence.lean) |
| Brouwer support | Determinant polynomial, no smooth retraction, ball fixed point and convex-domain extension | [DetPoly](RequestProject/Brouwer/DetPoly.lean), [NoRetraction](RequestProject/Brouwer/NoRetraction.lean), [Ball](RequestProject/Brouwer/Ball.lean), [Convex](RequestProject/Brouwer/Convex.lean) |
| Theorem 5 | Unique equilibrium under contraction; discrete/continuous rate bounds and evidence sensitivity | [Contraction.lean](RequestProject/Contraction.lean) |
| Theorem 6 | Nonincreasing potential and equilibrium limit points under compactness, continuous potential and unique coordinate minimizers in cyclic repair | [Potential.lean](RequestProject/Potential.lean) |
| Proposition 7, partial | Unique equilibrium of the clipped two-node map, nonconvergence from other starts and square invariance | [TwoNodeLoop.lean](RequestProject/TwoNodeLoop.lean) |
| Proposition 8; Corollaries 9–10; Proposition 11 | Average balance, affine-repair limit points, rate law, closure gap and integrated charge balance | [Averages.lean](RequestProject/Averages.lean) |
| Theorem 12 | Two-sided equilibrium displacement bounds and detuning | [Contraction.lean](RequestProject/Contraction.lean) |
| Theorem 13 | Equilibrium-propagation derivative identity under smoothness and a differentiable stationary branch; related learning identities | [EqProp.lean](RequestProject/EqProp.lean) |
| Sections 5.1 and 5.3 | Finite descent, Newman's lemma, normal forms, cycle obstruction, noise bounds and selection identities | [Layers.lean](RequestProject/Layers.lean) |

[`RESULTS.md`](RESULTS.md) gives the exact Lean declaration names. [`Main.lean`](RequestProject/Main.lean) imports the main modules and prints selected axiom dependencies.

## What the formalization does and does not establish

The supplied result map records these boundaries:

- **Proposition 7:** the periodic-orbit claim is not formalized. The implemented nonconvergence and invariance results are narrower; the report identifies Poincaré–Bendixson as the missing step.
- **Theorem 5(3):** the relaxation trajectory is explicitly assumed to remain in the domain.
- **Proposition 8 and Corollary 10:** the relevant repair map or signals are assumed continuous.
- **Proposition 11:** the spiking result is stated in integrated form.
- **Theorem 6:** equilibrium limit points do not imply that the entire sequence converges to one point.
- **Excluded:** the Section 6 simulations and externally cited results such as asynchronous convergence, Kakutani, Nash, Arrow–Debreu, Aumann, DeGroot, sheaf heat flow and OPH reconstruction.

Formal results establish consequences of their encoded hypotheses. Identifying a physical, neural, biological or economic system with those hypotheses requires separate modelling and empirical evidence. The paper's universality thesis is not established by a successful Lean build.

## Reproduce the checks

With Git and a Lean installation managed by `elan`, clone the repository and use its pinned toolchain and dependency manifest:

```bash
git clone https://github.com/enuminous/Aristotle-Agreement-and-Surprise-Global-Equalibrium-from-Local-Repair.git
cd Aristotle-Agreement-and-Surprise-Global-Equalibrium-from-Local-Repair
lake build
lake env lean RequestProject/Main.lean
```

The final command prints the selected axiom dependencies. Consult the complete theorem statements for their assumptions; an axiom list is not a list of modelling premises. The first build may need to download the toolchain and dependencies.

## View the landing page

[`index.html`](index.html) is a responsive, standalone page with inline CSS, JavaScript and SVG. It needs no build step, external fonts or third-party scripts. Open it locally or serve the repository root:

```bash
python3 -m http.server 8000
```

Then visit `http://localhost:8000/`. The same file can be served by GitHub Pages from `main` / root when Pages is enabled. Adding the file does not itself enable hosting.

The page includes a labelled synchronous-repair illustration. Its contraction example is $R(x,y)=(y/2+1/4,x/2-1/4)$, with fixed point $(1/6,-1/6)$ and contraction factor $1/2$ in the maximum norm. The second example uses the exact clipped map from `TwoNodeLoop.lean`. These finite numerical illustrations are separate from both the formal proofs and the paper's Section 6 simulations.

## Attribution and related work

- **Paper:** Bernhard Mueller, Pragma Research Inc., _Agreement and Surprise: Global Equilibrium from Local Repair_, draft, 6 October 2026. The [included PDF](22ACBA52-C160-11F1-BAAE-D7B44D786CDB.pdf) is the source text.
- **Formalization:** this project was edited by [Aristotle (Harmonic)](https://aristotle.harmonic.fun). Its supplied run summary identifies run `9cf083ab-5270-4f61-9c03-a2ccf1cd5d6e`.
- **Repository:** Matthew Chenoweth Wright / [enuminous](https://github.com/enuminous). This is an independent repository; attribution does not imply the paper author's endorsement.
- **Related discussion:** [Cadence–OPH–EFMW common-core proposal](https://github.com/enuminous/oph-lab/blob/4182e37988001c8d7497bbe150351a0609a785c7/docs/CADENCE_OPH_EFMW_COMMON_CORE_PROPOSAL.md). That proposal is separate from the formalization hosted here.

The original Aristotle attribution guidance is retained: tag `@Aristotle-Harmonic` on relevant GitHub PRs/issues and credit its contributions with:

```text
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
