# TX2 fixture handoff — feasibility stop

Branch `codex/cx-joint-tx2fix-20261028`.
Stage 0 commit: `220881844b` (Record TX2 decoder and PDA feasibility blockers).
**Target not yet established. Stage 1 and Stage 2 not entered.**

## Before / after and exact residual obligations

Before: `JHj_Authentication.source` proves the outer authentication caller only
under seven explicit observations, whose complete forms are enumerated in
`JHr_FEASIBILITY.md`. `JHj_TX2.after_validation` aliases
`JHi_TX2.after_validation`, retaining actual validate_asq8 success and the
three-equation `JHi_SHARealization.SHARealization`. The latter is the proof,
public-input and checksum SHA digest equations, not a decoder/PDA certificate.
Its three individual proofs are inherited; no new class instance is composed.

After: **identical statements and hypotheses**. Zero observations discharged,
zero hypotheses added, no carrier/fixture/implementation changed. No JHr_TX2
or JHr_Joint theorem is supplied. No compile success, memory peak, axioms
closure or joint non-vacuity result is claimed for either target.

The desired same-SDK TX2 conclusion remains:

```lean
S2W_D189Wrappers.second (JHe_Natives.second base stage)
  CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
  JHb_DataRequest.value (.Ok slot) () =
    ok (.Ok (JHg_World.e2.heap,()))
```

Here the free fields of base must actually be filled by the specified faithful
functions. It cannot be inferred for arbitrary unconstrained base callbacks.
The saved checkpoint bytes stay exactly JFx_NativeBytes.checkpoint, as fixed
by JHn_ExactReturned and JHq_TX1. No independent TX1 output was selected.

Inherited `JHq_TX1.accepted1_saved` retains **only** JHe_SHARealization, the
453 concrete tree SHA equations (157/157/139); this task neither proves nor
changes that class. No new PDA digest/off-curve certificate class is declared.
In particular the seven successful callback observations are **not** packaged
as certificate fields. Their implementation bodies are missing source inputs,
not admissible cryptographic assumptions. Exact PDA hash/off-curve equations
can be stated only after fixing the actual SDK model and its byte encoding.

`JHn_Joint.assembleJoint` consumes JHn_TX1Frontier.ByteIdentity and a TX2
accepted2; it does not consume JHq_TX1.accepted1_saved directly. It uses the
corrected TX1 world/post. JHn_ExactReturned.source already provides the byte
identity, but accepted2 is still absent. No 8 GiB join/import test was run;
therefore there is no peak to report and no reason to invoke the lead's
separately authorized agg16 path.

## Concrete blocker and next deliverable

The generated-final cohort FunsExternal_Template declares:

- decode_master_box, decode_checkpoint_box, decode_lane_from_pool_release:
  external **axioms**, not function bodies (lines 502/510/518).
- Pubkey.create_program_address: external **axiom**, mapped to SDK
  solana-pubkey 2.4.0 lib.rs:911–914 (line 436).
- Registry/entry V2 decoder children: also external declarations.

AdapterRwModel.Ops.op38 is free, as are op48/op49/op50. The inherited leaf
installers leave op38 unfilled. NBX installed-slot theorems prove retention;
row/frame/codec theorems are structural ingredients, not definitions or
whole-decoder evaluation laws. PoolS2 PDA caller lemmas also retain the actual
SDK create result. An older September extraction has differently named
v7_pair_forest_dispatch decoder bodies; no unproved cross-cohort equivalence
was adopted.

Next deliverable: coherent extracted bodies for the three requested decoders
and registry children, plus the actual PDA runtime model/association. Then
follow the field/row routes in JHr_FEASIBILITY and introduce only exact named
SHA/off-curve certificates at their real boundaries. This report does not
establish that no such source exists elsewhere; it identifies its absence
from the supplied cohort and the precise artifact needed to proceed.

## Validation, resources and preservation

Read /Users/dominic/ZK/AGENTS.md including Security and proof discipline,
local-lean.txt rules 1–14, both required handoffs and the referenced symbolic
support/interface sources. Static source hashes, external declaration excerpts
and tracked-tree definition-search command/output are committed alongside this
handoff. No new Lean module, theorem, nonstandard axiom, sorry, dictionary,
constant-success callback, concrete reduction, launcher or monitoring code.

Budget: **0/80 Lean, 0 Kani**. No cgroup/admission request, cache build, package
replay, full manifest or runtime gate. Peak RSS/wall/swap/axioms for proof
compiles are inapplicable, not zero-valued measured results. Seed caches were
read only; own cache not initialized because feasibility stopped before build.
No source/ELF/headline/security credit, wallet/key operation, push, merge or
other-worktree edit. Only this task's evidence is changed.

The initial evidence git-add was refused by sparse-checkout; adding the exact
owned evidence path fixed the input error before the Stage 0 commit. No prover
was launched or repeated. Final checks: owned evidence has no file over 20 MB;
source/evidence whitespace check and committed-scope check pass. The deployed
100-bit target and joint acceptance remain not established.
