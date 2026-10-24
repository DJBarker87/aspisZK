# S6 named full-forest port and two-transaction consumer — 2026-10-24

**Proved:** the exact named `S2Y_ForestPublic.FullForestAcceptedRoundtrip`
interface for the concrete current codec/first installation, and its use in
the original two-transaction owned public-field consumer. **Whole S6 and the
actual-release 100-bit target remain open.** No production source, frozen
artifact, security metric or other session's source was changed.

## Before and after

The lead's unchanged `S2Y_ForestPublic.owned_public_field` takes:

```
ops : AdapterRw.Ops
fullForestAcceptedRoundtrip : FullForestAcceptedRoundtrip ops
childInputRetention : ChildInputRetention ops c
accepted1 : stage1_owned ops ... = ok (.Ok checkpoint1)
accepted2 : stage2_owned ops ... = ok (.Ok ())
```

The checked `S6CurrentNamedForestPortV1.owned_public_field` uses the SAME full
AdapterRw statement/account/error/Result carriers and the SAME accepted parent
calls and conclusion, with `ops` specialized to
`AspisS6CurrentFirstInstallation.install adapterOps verifierOps`.
It supplies `fullForestAcceptedRoundtrip` by theorem, rather than accepting it
as a premise. The installation contains the concrete current decoder, original
outer encoder and current first/tx1 child; remaining Ops fields are retained.
This is a concrete specialization with discharge of its codec premise, not a
claim that every arbitrary ambient Ops record satisfies the codec law.

`S6CurrentNamedForestPortV1.fullForestAcceptedRoundtrip` has exactly the lead's
named Prop as its conclusion. It composes the existing concrete original
native outer codec inverse, the complete native/current statement and error
bijections and the actual extracted boxed decoder control. All original bytes
are equal, including the complete common, late and payment fields of the
1,880-byte format. No hash-only, payment-only or 320-byte substitute is used.

`S6CurrentNamedForestPortV1.reconstructed_bytes` applies the unchanged named
consumer and obtains equality of the actual encoded/original bytes and length
1,880. `owned_public_field` applies the existing complete owned two-transaction
consumer. Public/proof arguments, encoder/decoder successes, checkpoint and
first/second calls come from those same accepted parents; independent child
successes are not added.

## Exact retained obligations

The new public-field theorem still takes `ChildInputRetention` for the reached
first/second children and the two accepted owned executions. Its final byte
and reached-public-input conclusion still has the original antecedent
`validated.statement = statement`. Neither child trace provenance nor
cross-transaction reconstruction identity is inferred from codec equality.
The original `c`, program, accounts, data, slot, returned checkpoint and
remaining adapter/verifier operations are still quantified.

Actual SDK/allocator/abort/ordered-effect correspondence and concrete native
child interpretation remain separate source-boundary work. This result does
not instantiate S2's complete native wrapper extraction record or prove all
other verifier cone backends. The latest S2W authentication route can avoid
this codec premise; the result here nevertheless closes the named full codec
port requested by the lead, and the original S2Y consumer now uses it.

No new source-adoption decision is requested. Any future adoption of a changed
Rust claim/adapter or release artifact still requires its explicit equivalence,
source/artifact and affected-parent re-pins. The existing release authorities
and exact codec source pins remain those recorded in
`S126-CURRENT-CALLER-INSTALLATION-20261024.md` and its source-pin packet.

## Validation, reused evidence and trust

Accepted target: `S6CurrentNamedForestPortV1`, attempt
`s6-current-named-forest-port-v10`, exit 0, wall 63.980441584 seconds, peak RSS
4,334,911,488 bytes, zero swap. The focused command was `lake env lean -j1
-M4400` under the shared atomic local lock. All three public theorems report
only `propext`, `Classical.choice`, `Quot.sound`.

The exact final source, command, tool hashes, import roots and receipt are in
`evidence/s126-current-caller-20261021/s6-current-named-forest-port-v10`.
The `s6-current-named-forest-port-{import,companion,tool,reused}-pins.json`
files identify the selected dependency and tool artifacts by hash, including
available `.olean.server`, `.olean.private` and IR companions as hashes only.
No compiled object or IR is distributed.

`evidence/s126-current-caller-20261021/s6-current-named-forest-reused` retains
the unchanged S2Y geometry, owned-children, full-forest and audit sources with
their original green receipts. Their source hashes match current research.
Their existing checked proofs were reused; no unchanged full replay ran.
The named consumer dependency closure was imported and the new application
checked, but this is not a fresh coherent release rebuild.

The first import attempts exposed partial-root lookup and old generated-name
collisions. A private cache union selected the already checked repaired
`R1SemanticHit` object (`09f6d44c…`, producer packet
`evidence/lean-semantic-import-join-20261015/source-manifest.json`) and the
canonical raw-model objects from the existing S2I/S2Y import union. No source
or proof statement was modified to suppress a conflict. Final object hashes
are explicit in the import pins. Failed attempts v1–v9 are excluded from
accepted evidence; v9 also contains Lean's error-generated `sorryAx`, and is
not a proof. The final target has no custom axiom, hole or resource override.

Audit:

```
python3 tools/s6-full-forest-roundtrip-20261023/check-named-forest-port.py
```

Next enclosing obligations remain the concrete native source/SDK interpretation
and child trace/statement identity joins stated above, alongside S1's original
native claim correspondence. The ≤2^-100 per-attempt target is unchanged.
