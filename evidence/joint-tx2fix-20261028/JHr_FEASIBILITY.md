# TX2 fixture feasibility — Stage 0

Status: **STOP before Stage 1: required cohort decoder/PDA definitions unavailable.**
Source revision: `6eda25585aadc266b177836576a76082e759a070`.
Branch: `codex/cx-joint-tx2fix-20261028`. No Lean/Kani process launched.

The supplied generated-final external template declares the required functions
as **axioms**, not executable extracted definitions. Earlier progress commentary
called them `sorry` placeholders; the exact syntax is `axiom`, as recorded in
`JHr_EXTERNAL_SLOTS.json`. Neither kind is an admissible implementation here.
The adapter model replaces these external declarations by `Ops` fields; it
does not supply their source bodies. This is a missing implementation/source
association, not a failed computation, a cryptographic assumption, or evidence
that the fixture rejects. No external-template axiom is imported or adopted.

## Exact seven inherited obligations and intended routes

Notation below is textual shorthand only: `o = JHd_ReferenceSlots.install base`,
`e2 = JHg_World.e2`, `pool = JHb_Programs.pool`, and `slot : U64`.
Every observation below is copied from `JHj_Authentication.source`; there is no
new dictionary, renamed carrier, or changed fixture.

1. Master decoder:
   ```lean
   o.op48 JHg_DataMaster.value = ok (.Ok JHg_AccountValues.master)
   ```
   Required selection: actual cohort `r1_pool_adapter.decode_master_box`.
   Route: split length/magic/version/binding, identity and policy fields;
   transport the eight original byte-reader sequence fields through
   `NBX_RowFrames.value_frame`, `NBX_FrameComposition.rows_value`,
   `NBX_SequenceResult.returned`/`capacity`; compose the real decoder guards,
   error mapping and Box return. NBX's installed-op theorem proves retention
   only. The wrapper is an external axiom at template line 502, so the proposed
   composition has no available extracted body. No large reduction attempted.

2. Master PDA:
   ```lean
   o.op38 JHj_Seeds.master pool = ok (.Ok JHj_Seeds.key)
   ```
   Route: actual SDK create-program-address seed-count/length guards, ordered
   seed concatenation, program ID and PDA domain suffix, then an exact named
   SHA digest equation and exact named Ed25519 off-curve certificate; transport
   the returned 32 bytes to `JHj_Seeds.key`. No kernel SHA/curve reduction.
   The SDK implementation is external, not defined by the cohort (see below).

3. Registry authentication (the seventh-child accounting includes this whole
   compound obligation, not merely a third PDA):
   ```lean
   r1_pool_adapter.owned.authenticate_invariant_release_registry o
     CPH_Program.verifier pool (e2.snapshot 1 384 384)
     JHg_AccountValues.master (e2.snapshot 4 128 256)
     (e2.snapshot 5 192 320) slot = ok (.Ok ())
   ```
   Route: reuse JHj_RegistryReady/Reads/Fields/Checks and Entry counterparts;
   instantiate real policy/status functions using NBX_SlotValues and
   NCF_EntryContract.op29_exact; decode original registry/entry bytes with real
   op33/op34, supply the loader ID, and derive four actual PDAs on
   JHj_RegistrySeeds.registry, registryProgramdata, entry, verifierProgramdata
   with their actual program IDs. Each PDA needs its own named digest/off-curve
   equations. This is not discharged by the existing row laws or raw expected
   records. The registry decoders are also external declarations in this
   template (lines 384 and 396–400); the PDA body is absent.

4. Checkpoint decoder:
   ```lean
   o.op49 JHg_DataForest.value = ok (.Ok JHg_AccountValues.checkpoint)
   ```
   Required selection: actual cohort `r1_pool_adapter.decode_checkpoint_box`.
   Route: split header, master/domain/sequence, canonical digest and eight lane
   sequence fields; use inherited field/row and capacity laws, then compose
   actual guard/error-map/Box return. The external template declares the
   wrapper as an axiom at line 510. Retention of op49 does not prove decoding.

5. Checkpoint PDA:
   ```lean
   o.op38 JHj_Seeds.checkpoint pool =
     ok (.Ok (e2.snapshot 2 192 192).key)
   ```
   Route: same SDK symbolic derivation as (2), with the original master key,
   little-endian checkpoint sequence and stored bump; exact named digest and
   off-curve certificates. Blocked on the same missing SDK implementation.

6. Lane decoder:
   ```lean
   o.op50 JHb_DataLane.value = ok (.Ok JHg_AccountValues.lane)
   ```
   Required selection: actual cohort
   `r1_pool_adapter.decode_lane_from_pool_release`.
   Route: split lane/tree headers and reserved regions, master/lane/bump,
   next-leaf bound, current root and each frontier row; use NBN/NBU codec and
   window laws where applicable, prove canonicality/empty-subtree guards on
   individual fields, compose the actual decoder. Its 448–520 Rust body exists,
   but its Lean wrapper is an external axiom at template line 518. Generic
   window laws cannot rewrite this opaque function into a returned record.

7. Lane PDA:
   ```lean
   o.op38 JHj_Seeds.lane pool =
     ok (.Ok (e2.snapshot 3 768 768).key)
   ```
   Route: same SDK symbolic derivation as (2), using actual master key, lane 3
   and stored bump; exact named digest and off-curve certificates. Same blocker.

## op38 selection and fidelity

`AdapterRwModel.Ops.op38` (lines 92–94) is a **free slot** of type
`Slice (Slice U8) → Pubkey → Result (core.result.Result Pubkey PubkeyError)`.
The generated-final template identifies its native target as
`solana_pubkey.Pubkey.create_program_address`, solana-pubkey 2.4.0,
`src/lib.rs:911–914`, and declares that target as an axiom (line 436).
JHd_ReferenceSlots, JHd_KeyStd and JHe_SdkLeaves do not fill op38. Consequently
this task cannot name an already defined, faithful cohort PDA model to install.
PoolS2_PdaSource.Ops.create is another free child, not a PDA implementation;
PoolS2_PdaPrimitives.ready assumes the successful create result it transports.
Instantiating that result itself would retain the desired conclusion, contrary
to the requested digest/curve-only certificate boundary.

## What the search establishes

`JHr_SOURCE_PINS.json` pins inspected cohort/interface/support files.
`JHr_EXTERNAL_SLOTS.json` retains precise external declarations and origins.
`JHr_DEFINITION_SEARCH.json` records a tracked-tree search for definitions:
only older September `v7_pair_forest_dispatch` master/checkpoint definitions
were found, under distinct extraction namespaces. Those are not the requested
`r1_pool_adapter` cohort; no equivalence or conversion was assumed. The search
is not claimed to cover every untracked source on the build host. Read-only
inspection of the assigned seed caches and selected native-worker source
locations supplied no required decoder/PDA definitions.

The symbolic row/window lemmas are useful ingredients, but do not close the
original-reader, error, allocation, canonicality or caller association gaps
already stated in NBX_U04_BRIDGE and JHj_ASSOCIATION_GAP. Authorization to fill
free slots with real extracted functions does not create those functions.

## Admission decision

No available complete symbolic route to the **specified implementation** is
established. Large concrete reduction cannot recover an external body, so no
reduction, compile, certificate fabrication, or replacement dictionary is tried.
This is a source-availability feasibility stop, not a measured memory failure.
Stage 1 and Stage 2 are not entered. Required next input is the exact coherent
extracted decoder bodies and a faithful SDK PDA definition/association, or a
lead decision commissioning those separate missing source-refinement tasks.
No new acceptance or source-association hypothesis may replace that input.
