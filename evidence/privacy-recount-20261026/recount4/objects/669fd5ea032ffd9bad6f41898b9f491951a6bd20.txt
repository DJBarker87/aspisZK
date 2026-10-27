# Transfer: exact missing source-leaf association

Target not yet established. No actual selected Input term has been constructed.
The literal recorded public and transition terms are
`PV_RunJoin_RecordedTransfer.publicRecord` and `.transition`; they are data read
from the ed1c1cef71 terminal bytes, not a returned compilation.

The first source association not available in the supplied Lean closure is:

```
Records.call R_shipped w 600#u32 (some recipient) change snapshot 77#u32
  = @PV_Src_RecordDynamic.call E_shipped
      w 600#u32 (some recipient) change snapshot 77#u32
```

Here all arguments are the SAME transfer fixture arguments, not universally
chosen substitutes: `w` is the record built by
`v7_pair_forest_fixture::deterministic_input_witness_v1`, recipient is
`digest(300), digest(400), 600`, change is `digest(500), digest(600), 400`, and
snapshot is exactly `r0_fixture::prepare(false)`'s snapshot (pool [1;32],
domain [5;32], sequence/index zero, current_root empty[20], frontier
empty[0..20)). `R_shipped` means the extraction of the actual Rust records
function; it is NOT a currently provided concrete Lean constant.
`E_shipped` likewise means the deployed external-layer implementation.
This displayed proposition identifies the missing source interpretation; it
is not presented as a compiled Lean theorem or postulated as an axiom.

Shipped location: `crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs:227–270`
(`records`), called at `CopyRecords::new:297–306`, then by
`pair_forest_trace.rs:275` in `compile_forest_from_copies`.
The corresponding extracted boundary is deliberately opaque:
`BuilderForestAdmissionPort.lean:4362` declares `class Records`;
`:4376` defines the source records leaf to be `sourceRecords.call`.
`PV_Src_RecordDynamic.dictionary` is an owned reference, not an identified
instance of this shipped leaf. Its complete Result equation does not establish
that identification. Source pins are in source-pins.json; source bodies match
ed1c1cef71. No source-adoption fact is inferred from textual similarity.

The canonical transfer theorem at the pinned srcid3 revision is conditional
on canonical instance, roots, contexts, snapshot, compiled and anchor. Its
conclusion identifies only the returned private witness under the owned
reference. It does not instantiate R_shipped or return a full compilation.
The root certificate now covers 21/21 source constant cells, but that does
not identify the entire mapper, prove all compiler guards, or construct a
compiler return.

Per the requested missing-fact rule, stop this stage at this exact leaf.
Do not add another conditional admission/public-binding bridge. The desired
compiler-return equation and transition equality are still OPEN, not assumed:
`@PV_Src_NativeInput.run E_shipped R_shipped i = .ok (.Ok i.compiled)` and
`PV_Src_NativeInput.transition i.compiled.public_statement =
 PV_RunJoin_RecordedTransfer.transition`, at the actual selected i.
