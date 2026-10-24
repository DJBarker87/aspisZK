# Canonical stored carrier and headline transport (19:35 ruling)

Implemented in new modules only: `Port1_StoredCarrier`, `Port1_ParserCarrier`,
`Port1_CanonicalJoin`, `Port1_CanonicalHeadline`.

## Exact before / after

Before (`OraclePortFrozen2Join.AcceptedVerifierJoin`):

```
∀ H (i : Input), accepted (rust i) H →
  eval H (rust i) = eval H (verifier D dV_frozen2 i)
```

Here `i.proof : Nat → Message` was independent of `i.stored` and `i.statement`.
The existing impossibility theorem still applies to that statement.

After (`Port1_CanonicalJoin.AcceptedVerifierJoin`):

```
∀ (s : Submission) H, accepted (rust (input s)) H →
  eval H (rust (input s)) = eval H (verifier D dV_frozen2 (input s))
```

`Submission` has exactly two unrestricted byte lists, `publicBytes` and `stored`.
`input s` computes the proof by `OraclePortCompactDraft.parse s.stored`, then
`parsedProof`: initial root from bytes16..48, semantic rows from the strict
parser, expanded/framed late rows from `rowBytes`, and the literal constructor
schedule. Commitment words start at zero and are replaced only by annotation.
The public statement uses submitted public bytes and the stored variant tag.
There is no attacker-supplied logical function or semantic row witness.

`Port1_ParserCarrier.source_parse` applies the actual owned Aeneas parser cone's
`MultiproofConeParserTotal.accepted_parse` to the very same stored slice. It
proves returned decoded rows = the parsed semantic rows and canonical proof =
`parsedProof` of that parse. This reuses the parser source refinement, not just
an import of it. Adoption/lowering of the owned parser to production and S6
public-decoder transport remain their existing obligations.

For totality, malformed stored inputs use a fixed invalid payload proof;
public lists too long for the inherited 131072-byte address carrier use an
empty logical public list; oversized row payloads use empty payloads. These
are logical totalization branches, NOT new physical gates. `public_bytes`
proves exact public-byte identity under the inherited address bound. Runtime
admission/binding must justify use of the logical carrier for accepted source
runs, including the public bound. No actual source acceptance is inferred
from a totalization branch or from successful parsing alone.

Before headline (`OraclePortHeadlineFrozen2.final_soundness`):

```
(P : Program Bytes State Input)
(hqueries : ∀ H, (eval H P).1.length ≤ Q)
(join : OraclePortFrozen2Join.AcceptedRunJoin D rust)
(binding : StoredCarrierBinding D rust P runtime)
: Claims D P Q runtime
```

After (`Port1_CanonicalHeadline.final_soundness`):

```
(P : Program Bytes State Submission)
(hqueries : ∀ H, (eval H P).1.length ≤ Q)
(join : Port1_CanonicalJoin.AcceptedRunJoin D rust)
(binding : StoredCarrierBinding D rust (lift P) runtime)
: OraclePortHeadlineFrozen2.Claims D (lift P) Q runtime
```

The new run join has the byte-indexed raw field above and the same annotated
run equality, quantified over `P : Prover` whose outputs are `Carried` in every
oracle world. `Carried` allows only ghost-word changes: exact statement,
stored bytes and erased message equality to `input s` for some submission.
`two_pass` derives that annotated field from the byte-indexed raw field and
`Physical rust`; `driver_physical` proves the latter for `Port1_Driver.rust`
with arbitrary adapter/body dictionaries. This is a proved lifting, not a new
raw frozen2 identity assumption hidden in a carrier record.

`lift_carried`, `canon_lift_carried` and `enrich_carried` prove the actual
headline inputs at the original, canon and second passes are in that class.
`accepted_experiment` is the exact accepted equality consumed at the unchanged
`StoredCarrierBinding` boundary. `runtime_transport` preserves the complete
annotated view, extractor input and failure mass. Rejected runtime views still
have zero failure mass. No read prefixes are erased or reordered in this proof.
The complete old `Claims`, numeric constants, event, cost and bounds are reused.
`lift_queries` proves the lift issues no new prover calls.

Adversary submission power is unchanged: EVERY pair of byte lists is a
Submission, with arbitrary adaptive oracle programs returning it. No parse,
length, canonicality, honesty or success premise restricts that quantifier.
The correction removes an independent logical object that physical Rust never
receives. The runtime/carrier premise is still a required source obligation,
not asserted true, and the headline remains conditional on the raw join.

## Validation / scope

New focused host attempts013–016 all exit0; wall seconds respectively
2.140857045,2.084429147,1.934514041,2.350186440; maximum RSS4383732KiB, all
swap0. Exact targets/commands/source revision+hash/dependency objects/limits
and full axiom reports are in individual receipts. All new theorem audits
use only propext/Classical.choice/Quot.sound. No options raised, no timeout,
no kill, no Kani/Rust/full replay. Cumulative actual compiles15/100, Kani0/60.
No shipped source or ELF changed. This closes the canonical experiment lifting
and supplies a conditional headline with the corrected premise; it does not
close the raw source-to-frozen2/model-order port or the deployed runtime binding.
