# Owner decision: the trust link behind the native bridges (2026-10-28)

Status: DECISION REQUESTED. Lead recommendation below. Nothing is adopted until the owner decides.

**OWNER DECISION, 2026-10-28 evening: "take all your recommendatrions". All lead recommendations ADOPTED (option A; PDA item deferred; routes A and B in parallel; newer Kani sandbox evaluation only). Recorded as contract amendment (fifth).**

## The question in plain terms

The headline treats each deployed transaction as an opaque program (native1, native2) and assumes, as one premise (`extraction`), that it matches the model. The native bridges try to replace that assumption with evidence:
1. Kani proves that the real Rust code behaves like a plain Rust reference copy of the model's function, using contracts and controls.
2. Lean proves that the reference copy, translated by Aeneas, equals the model's function.

The two halves meet at one point that neither tool can prove: that Kani's reading of Rust and Aeneas's reading of Rust mean the same thing for these functions, and that the Rust entry points ARE the objects native1/native2 in the headline. NCQ_ checked this carefully (evidence/native-topspec-20261028/NCQ_TOPSPEC.md). It cannot be closed inside Lean. It is a statement about the two tools agreeing.

## Options

A. **Explicit clarification of existing tool trust (recommended).** Every Kani-plus-Lean bridge already relies on exactly this agreement, including the 13 closed opaque leaves. Recording it explicitly, scoped to the enumerated bodies, tools and versions in the receipts, makes an existing dependence visible; it does not add a new kind of trust. Effect: once the contract chain reaches the entry functions, the `extraction` premise is replaced by (i) checked Kani contracts with controls, (ii) checked Lean reference proofs, and (iii) this narrow, explicit tool-agreement row. That is a large reduction in what is trusted: we stop trusting the unchecked claim "the program equals the model" and trust only that two pinned tools agree on Rust semantics. It is still a reclassification under the counting rule, not a premise removed by proof, and it will be reported that way.

B. **Record it as a new trust row.** Same mechanics; the inventory shows one new row. Choose this if you consider the Kani/Aeneas agreement materially stronger than what the P6 bridges already assumed.

C. **Reject.** Then the native bridges remain supporting evidence only, and `extraction` stays a full premise of the release claim. The deployed target would then need a different route: a single verified toolchain from Rust semantics to Lean, which does not exist today.

## Draft row text (from NCQ_, for A or B)

"Native contract semantic transport (result projection). For only the frozen owned TX1 stage1, owned TX2 stage2 and SolanaDigest wrapper bodies, reference bodies, operation dictionaries, features, input/outcome encodings and tool versions enumerated by the accepted receipts, we trust that the Rust execution interpreted by Kani/CBMC and the reference execution interpreted by pinned Charon/Aeneas denote the same Rust language/primitive semantics under the certified common external world. We trust the explicitly recorded association of those Rust entries with the Lean function parameters native1/native2, of the digest wrapper with installed ops.op43, and of the external digest with hashv."

## What stays separate in every option

Source-to-ELF correspondence (the deployed binary is this source under the pinned toolchain); the K-1/K-2 Kani findings and their handling; runtime syscall, allocator and std rows; and the open item NCQ_ flagged, where release preparation/query/finish must be tied to the same pinned source by association evidence, not by tool trust.

## Second, smaller item: the address-derivation runtime call (test run only)

JHs_ (evidence/joint-pda-20261028/JHs_TRUST_PROPOSAL.md) modelled how the pinned Solana library derives program-owned account addresses, and proved all seven hash equations the TX2 test run needs. What remains for a faithful concrete TX2 run is the runtime call itself (sol_create_program_address) and its ed25519 "not a valid public key" check, which no current trust row covers. JHs_ drafted a narrow row, `FixturePdaRuntime`, limited to the seven enumerated calls. It matters ONLY for the concrete test run (non-vacuity), never for soundness, because the headline quantifies over this operation (ruling (s)).

Lead recommendation: DEFER this decision. The test run is also blocked on the three account decoders, which need real definitions from the contract approach first, so adopting the row now would not unblock anything. I will bring it back, with the off-curve facts either proved or isolated as the only remaining certificates, once the decoders exist.
