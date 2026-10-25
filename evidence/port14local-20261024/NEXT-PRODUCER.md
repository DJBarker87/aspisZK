# Port14LOCAL independent full-driver obstruction

This is a narrow design, not a new theorem or a new assumption installed into
the headline. `source-audit.json` pins every referenced source and ten reused
successful focused receipts, including their full commands, source/dependency
hashes, revisions, exit/time/RSS/swap and axiom reports.

## Exact source control to partition

`Port1_Driver.stages` executes TX1 at split 10 and observer None. Only its actual
`ok (.Ok saved)` return continues to TX2 with **saved.deref**. TX2's op18 returns
the actual Prepared/Accumulator used by its suffix. The static source contains
no stage loop or call recursion. Every inner Err, outer fail/div, checked-slice
failure and guard rejection truncates this chronology. A kernel proof of that
partition remains to be written; the audit is a source inventory, not that proof.

TX1 operation sites in source order:
`16,3,4,13,1,7,12,13,15,14,5(batch0),13,11,10,6,9,8,13`.

TX2 authenticated prefix then common body:
`3,13,18,16,17,13,23,22,2,0,15,14,5(batch1),13,11,10,6,9,21,20,19`.

Library IDs `{0,1,2,13,14,15,16,20,21,22,23,24}` have zero oracle reads by
Port1_Library.library_no_read, for every outcome, without assuming their success.
Direct slice/array operations are lifted pure Results. Owned op5(batch0), op8,
op18, op5(batch1) have unconditional all-H bounds 477,3,3,563 respectively.
These are at-most-once source sites, never four independently chosen successful
calls. Do not use general which values as if they were literal batch0/batch1.

| Delegated operation | Maximum executed sites | Actual argument dependence |
|---|---:|---|
| op3 | 2 | Same proof, in TX1 and authenticated TX2 prefix |
| op4 | 1 | TX1 proof, only after parser result |
| op7 | 1 | TX1 semantic/proof/D/hash/None and zero array[29] |
| op12 | 1 | S2; its accumulator feeds TX1 arithmetic/writer |
| op11 | 2 | TX1 prepared queries,0,10; TX2 resumed queries,a.next,22 |
| op10 | 2 | Actual current accumulator weights |
| op6 | 2 | Actual proof/prepared/accumulator/powers/geometry/weights, endpoint10 or22 |
| op9 | 2 | Actual returned pending weights and mutable weights slice |
| op17 | 1 | 29, actual resumed gamma |
| op19 | 1 | Actual final View/Prepared/updated accumulator/None |

Full dependent Call constructors and Implementation type are copied verbatim in
`retained-interfaces.lean.txt`; no callback structure hides the missing work.

## Exact missing producer and consumer

Required input is a **named concrete source-associated** implementation R of
type `{A : Type} → VTop_Trace.Call A → Program Bytes State (Result A)`, supplied
by the existing delegated source owners. R cannot remain arbitrary, or be chosen
as a no-read/always-reject implementation merely to establish this budget.

For each delegated ID j above, its producer must prove this numerical statement
with its concrete weight `w j : Nat` (all H, all actual arguments, all outcomes):

```text
∀ {A : Type} (call : VTop_Trace.Call A) (H : Bytes → State),
  VTop_Trace.operationId call = j →
  (eval H (R call)).1.length ≤ w j
```

The explicit remaining numerical obligation is

```text
2*w 3 + w 4 + 2*w 6 + w 7 + 2*w 9 + 2*w 10 + 2*w 11
  + w 12 + w 17 + w 19 ≤ 115.
```

No values for these weights, or concrete R, are supplied by Port12/13.
For example the op3 producer in its full argument domain is exactly
`∀ (proof : Slice U8) (H : Bytes → State),
 (eval H (R (.op3 proof))).1.length ≤ w 3`;
it must count the rejected parser prefix too. This statement contains no native
totality, source/model output equality, accepted-run or unexecuted-read success.
If only reached-domain bounds are provable, explicitly prove the source
invariant at the corresponding site; do not assume it or restrict the prover.

The concrete consuming target, after those actual producers exist, is

```text
∀ (adapter : AdapterRw.Ops) (ops : VTop_Stages.Ops) (reserved : Bool)
  (unwrap : Port6CK_Semantic.Unwrap) {X : Type}
  (D : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X)
  (H : Bytes → State) (i : OraclePortStoredExperimentC4.Input),
  (eval H (Port1_Driver.rust adapter
    (Port9OR_Installed.implementation ops reserved unwrap R) D hash i)).1.length ≤ 1161
```

This target's proof must partition the actual TX1/TX2 tree, use all-outcome
bind-length addition, and prove its owned sites occur at most once in the
specified order. Source returns determine every next argument. Error branches
use only their executed prefix. Decoder rejection contributes zero. No equality
to `Port12COUNT_Installed.checkpointChain` is asserted or needed. Avoid reducing
the batch bodies: apply their existing symbolic bounds directly.

Then Port6AUTH_Accounting.budget consumes that one-driver bound plus Physical
and the unrestricted byte-prover query bound, yielding source first reads
≤Q+1161. Annotation executes two verifier passes: source **total** log is bounded
by Q+2322, while repeated-pass first reads use Q+1161. These metrics must stay
distinct. No fresh-query assumption is introduced.

## Actual blocker, not an absent wrapper

For every finite N, an admissible unrestricted R can implement op3 as N asks
followed by `.done (.fail .panic)` and every other constructor as immediate
failure. The typed Result permits that at every result type. In
`Port1_Driver.stages` the installed op16 returns10, so TX1 split10 reaches op3;
`interpret` appends all N reads before stopping on that failure. N=1162 already
violates the proposed whole-driver1161 bound even though acceptance is false.
If lifting to `rust`, take an input/adapter for which decodeSemantic succeeds;
the stages obstruction itself requires no decoder premise. Repeated addresses
still count as calls; choose distinct byte addresses if testing first reads.
This is a source-definition counterexample argument, not a new compiled Lean
counterexample or a deployed malformed fixture.

Likewise no concrete runtime is fixed at this interface. StoredCarrierBinding
still means exactly `∀ H run, (eval H runtime).2=some run → run.2.2=true →
run=eval H (annotatedWith decoder rust (canon P))`. Merely constructing the RHS
as a new runtime does not identify a deployed run. Port6AUTH_Probability already
transports it to source failure; no transport wrapper is missing.

The other independent producer is CleanAcceptedModel for the actual source:
for every H, source acceptance and exclusion of source `bad` must yield terminal
Checks and classifier no-hit on the exact reconstructed transcript. The full
definition is preserved in retained-interfaces. Authentication recovery supplies
selected payload equality under its retained parse/query/root/frame/no-hit
premises; it does not supply terminal checks or classifier domination. Parser,
prepare7, powers17, sampler, primitive and S6/S10 remain the delegated frontier.

No theorem statement changed: before and after are the same exact statement in
`unchanged-endpoint-statement.txt`. No source obligation is claimed discharged
by this design. Stop here because callback witnesses are redundant and the
remaining concrete producers belong to the recorded Session A frontier.
