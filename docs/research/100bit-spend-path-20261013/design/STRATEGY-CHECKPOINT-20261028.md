# Strategy checkpoint for the owner (lead, 2026-10-28 evening)

Plain-language summary of where the soundness work stands, what the day's results mean, and the choice ahead. Target not yet established.

**OWNER DECISION, 2026-10-28 evening: "take all your recommendatrions". All lead recommendations ADOPTED (option A; PDA item deferred; routes A and B in parallel; newer Kani sandbox evaluation only). Recorded as contract amendment (fifth).**

## Where we are

- **The headline theorem** (AspisR1.RPx_Deployed.deployed) has no open premises on its own statement (83T/0P/13G, with L154 as the statement parameter). What remains is:
  (1) its trust items (the 83 T rows), the largest being that the deployed program matches the model (the `extraction` premise, narrowed by D188);
  (2) the 13 game/runtime statement items;
  (3) three deployment items: the joint real-byte walkthrough (non-vacuity), the final trust/axiom audit with the source-to-binary step (L188), and S10 completeness.
- **Native bridges** (the work of most jobs today) exist to SHRINK trust item (1). They prove, function by function, that the real Rust code matches the model.
- **Done:** all 13 directly proved functions (opaque leaves) stand as local bridges, re-checked after both Kani faults and the build-settings audit. The transaction-1 accepted run is proved to exist with exact saved bytes. The checkpoint caller domain is proved for every reached call, apart from three named field conditions. Batch authentication for both transactions is composed down to 18 precise per-step native facts. Every credited native result is checked against the deployed build settings.

## What the day showed

1. Native per-function bridging works but is slow. Many units are proved in pieces and stall at joining pieces into one run.
2. Joining cannot happen in Lean, because the headline treats each transaction as one opaque program. It can happen in Kani through function contracts, but on the pinned Kani version contracts work only for functions returning simple values or fixed arrays. Functions returning slices or growable lists cannot be substituted by their contract, and loop contracts crash.
3. Even when contracts join everything, the final link (Kani's reading of Rust equals the Lean objects in the headline) is a trust statement, not a proof. That is the pending decision in COMPOSITION-TRUST-DECISION-20261028.md.

## The choice

A. **Release route (recommended to run now, alongside B).** Finish the three bounded deployment items: the TX2 walkthrough (its decoders are being built now), L188 and S10. Then state the result honestly: the 100-bit bound is machine-checked for the deployed program, conditional on an explicit, owner-accepted trust inventory whose largest item is that the program matches the model. That is the strongest honest claim available without (B) or (C).

B. **Trust-reduction route (continue in parallel).** Keep native bridging to shrink that trust item. Contracts are used where the pinned tool supports them; elsewhere the evidence is assembled into a written, audited call-graph composition argument. This produces strong evidence and a much narrower trust item, but on today's evidence it is a long programme (hundreds of functions) with no fixed end date.

C. **Toolchain route (needs your approval to evaluate).** Test a newer Kani release in a sandbox for contract support on slice and Vec returns and loop contracts. It would be adopted only after re-running the K-1, K-2 and contract fidelity controls on it. A tool change needs your approval because it changes a pinned trust component.

## Decisions requested

1. COMPOSITION-TRUST-DECISION-20261028.md option A, B or C (recommendation A).
2. Whether to pursue routes A and B in parallel as above (recommendation: yes).
3. Whether to evaluate a newer Kani in a sandbox (route C). Recommendation: yes, evaluation only, with no adoption without a further decision.
