# Constructive complete stage1 reference on original inputs

S2/S1/S6 and the 100-bit per-attempt target remain OPEN. This packet closes
the complete installed-reference construction obligation. It does not claim
that its hypotheses have all been instantiated by one frozen native SDK run,
or that the14-field lead interface or cross-transaction transport is complete.
No production Rust, SDK, wire, parameters or ELF changed.

## Enclosing obligation actually closed

`S2SdkReadyRawInputsV1.ReadyRawInputs.construct` (full name starts
`AspisS2OwnedStage1.SdkReference`) constructs the COMPLETE installed borrowed
stage1 execution on the ORIGINAL full three-account/data records. Its
conclusions identify the original proof/public byte views, the exact supplied
first-result checkpoint in account2, the full CP-only byte-vector heap update,
unchanged account/lamport metadata, and the current verifier child called with
observer None and the same public/proof/k/checkpoint.

There is no whole stage1/body/helper/write/release success premise. There is
no independent common-field or semantic-public witness. Both getters are
proved total on the SAME decoded statement. The same native-required metadata
parametrization is proved equal to the ORIGINAL records; no flags, owners,
rents, slots, byte vectors, counters or Rc fields are silently initialized to
make execution succeed. CpFree is an explicit input fact, not an update to an
unrelated initial state. The initial proof prefix, tag and checkpoint bytes
are NEVER overwritten by this constructor.

The exact public inputs are:

- Original full records pa/ua/ca, p/u/c, the complete lamport vector, program,
  mode10or11, decoded full statement, encoder candidate and first checkpoint.
- Necessary metadata: readonly flags and slots0/1 for proof/public;
  checkpoint owner=program, nonsigner/writable/nonexecutable, slot2; its original
  counter0; distinct keys. Full unmentioned metadata is retained.
- Source sizes58295/1768/1768, allowed proof/public signed counters, all original
  checkpoint bytes zero, original proof.take688=candidate, original byte696=2.
- Exactly FOUR source-call observations: `decoded`, `validated`, `encoded`,
  `firstReturned`. Decoder/validator/encoder are installed concrete source
  helpers; first is the installed current-child call on the same statement's
  derived public value, original public bytes and proof suffix [688,58295).

SDK acquisition, scan/comparison/index success, independent projection success,
copy/write success and finalizer success are derived. Checked adds688+57607
and688+8, actual range operations, both instructions' byte1 access and U8→usize
casts, checkpoint size1768, source Vec clones and release termination reuse
checked source/library lemmas. Actual source operation order is retained:
checkpoint acquisition→scan→public acquisition/decode/validate/encode→proof
acquisition/gate→first→write→release. No new order or error path is installed.

## Before/after statement and domain audit

Before, the enclosing export
`CheckpointWriter.borrowed_stage1_sized_account_image` required

```
BorrowedReference.owned_stage1 (Installation.install ops verifierOps)
  program initial instruction = ok (.Ok (), out)
```

and extracted its fixed-input/current-first/checkpoint/metadata witnesses.
The new constructor DERIVES that full-run equality and the supplied checkpoint
image from the raw conditions above; `ReadyBody.construct` explicitly proves
its concrete body result and derives its live-guard invariant, actual finalizer
return and post-write byte frame. `ReadyStatement.construct` removes common/
public projection premises; `ReadyOriginal.construct` removes the metadata
parametrization equality premise; `ReadyRawInputs.construct` removes partial
scan/comparison/index/borrow-operation observations in favour of raw facts.

This is NOT advertised as a weaker premise over every old OwnedSdk. The new
contract explicitly parametrizes three canonical slots and supported
instructions, and requires the necessary successful child/admission facts.
The old arbitrary-state accepted-run export is retained unchanged. Native
accepted-class completeness and representation must establish that this new
class covers the frozen runtime executions. Full-model account objects and
all their fields are used; this is not a Boolean or opaque substitute SDK.

Classification: conditional forward/source-reference result, not TOTAL for
arbitrary malformed inputs or arbitrary failing/diverging children. Its
primitive key/owner comparisons and statement getters are TOTAL at their stated
types; instruction/index/cast facts are total on both supported instructions.
Arithmetic/borrow/write/release success follows on the explicit ready class.
It does not close whole-cone R22, source SDK execution or the security experiment.

## Exact source and validation evidence

Six smallest changed modules compiled individually with warm imports and atomic
`/tmp/aspis-local-lean.lock.d`, -j1 -M4400. No cold dependency build or unchanged
full replay. The attempted import of an existing generic equality module lacked
its protocol-model object; after checking warm caches, only its three generic
proof bodies were reused verbatim under a local namespace/import. No other
cone's file was changed, and the unrelated protocol dependency was not built.

| Module / accepted attempt | Exit | Wall s | RSS bytes | Swap | Axiom reports |
|---|---:|---:|---:|---:|---:|
|S2SdkKeyEqualityV1 / v1|0|21.645107375|3227582464|0|3|
|S2SdkReadyCallerV1 / v6|0|19.597707625|3267526656|0|6|
|S2SdkReadyBodyV1 / v6|0|19.212176708|3339730944|0|1|
|S2SdkReadyStatementV1 / v2|0|19.382863167|3268886528|0|3|
|S2SdkReadyOriginalV1 / v2|0|19.607041500|3300507648|0|4|
|S2SdkReadyRawInputsV1 / v1|0|20.973173250|3265363968|0|4|

All21 audit reports contain only propext/Classical.choice/Quot.sound (some a
subset). No sorry, custom axiom, native_decide or resource-option override.
Per-attempt source snapshots, exact Lean/lake/import/object hashes, command,
exit/wall/RSS/swap and full audits are retained. Current receipts' source parent
is ccae116a5d. `ready-caller-import-pins.json` pins the exact dependency closure;
compiled binaries are not distributed and this is not a coherent release replay.

Historical failed drafts are excluded; ReadyBody-v4 was a checked weaker
forward-result predecessor superseded by the actual saved-output/heap-frame
result in v6. Metadata/record layout syntax, standard unsigned-cast reflection
and source getter-head normalization errors are retained transparently. Two
missing-import preflights launched no Lean; their missing historical source
snapshots/timing are explicitly recorded as unavailable, never proof evidence.

Source freeze: historical b2727acd3abf79315d18b754a260f58f4b1c6326; adopted
25866ec331cc7ce27dd9956609c11d32fa8fa58a with S4 adoption
29cbab431742f7e899870595167efa193a379f0a. Research inspected read-only at
e23e12591f (C3-BIN latest adoption/interface addendum still12:40). Four caller
files remain byte-identical to the adopted/historical caller bodies;
`ready-caller-source-overlay-20261022.json` records exact hashes. Default/devnet/
Pool pins remain40dc7574/12cb0bc2/121f3e29. No old transitive S4 proof or binary
certificate is silently transferred to the adopted source.

Audit without replay:
`python3 tools/s126-sdk-modular-20261021/check-ready-caller-packet.py`.
It checks exact sources/receipts/import pins, all21 standard axiom reports,
verbatim generic proof reuse, original-input constructor scope, the FOUR
remaining call observations and absence of helper/whole-caller success
premises. It explicitly reports native_sdk_closed=false.

## Remaining native/caller obligations

1. Instantiate these raw guard facts and FOUR call observations from the SAME
   frozen native successful execution and fixed external proof/public inputs.
   Reuse native constructor-ready v4, actual17 first-entry windows, actual
   scanner/gate/iterator laws and accepted-prefix/output-length cut v13/source-v9.
   Prove the common execution/prefix-causality and actual child interpretation
   links; independent green facts do not supply those links automatically.
2. Compose the concrete native copy, actual implicit cleanup, actual SDK region
   geometry and native source order into the original native output account
   frame. Keep typed-value movement, actual allocation/deallocation dispatch,
   general runtime/ABI/P6 and account-state representation qualifications.
   The native-first complete paired check remains valid in its old qualified
   class; timed-out initial-clone/reversed full pairs remain excluded.
3. Instantiate the per-call Solana hash/ROM and source child/query/oracle
   interpretations. `ops.op10/op11` and the concrete verifierOps instance remain
   actual syscall/error/child boundaries, not consequences of byte preservation.
   No new collision term/query budget or probability metric is introduced.
4. Fill the lead's14 caller fields, including TX1 save→account→TX2/resume and
   fixed public reconstruction/retention. Hash equality alone is not byte
   identity. Original Pool ASQ8, reconstructed ASF8 and verifier CP are distinct.
   Import parser/multiproof results rather than redo their owned cone proofs.
5. Consume the resulting actual caller connection for S6 decoded-public reuse
   and S1 original Prepared/new/prepared_claim challenge trace, remaining totality
   and adopted-source re-pins; perform the final coherent closure audit/replay.

No source/protocol adoption decision was made or requested. The next task is
actual native-instance composition, not another whole-stage timed-out replay.
