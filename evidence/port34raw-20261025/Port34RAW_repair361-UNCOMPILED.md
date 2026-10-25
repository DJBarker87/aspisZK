# Actual361 proof-tail and motive repair proposal — UNCOMPILED

Call361 succeeded as raw data IO only. Full actual Calls and Bridge types and
selected hidden-structure types are in Port34RAW_actual361-types.txt. Exact raw
CI exports and all complete rendered values stay at /private/tmp/Port34RAW-361-20261025,
pinned by attempt-361.json. The 101,259,737-byte JSON is external; do not dump it.
Port34RAW_inspection361.json records finite string counts, excerpts and character
offsets in decoded value_rendering strings. These are rendering positions, NOT
Expr paths, AST node identities, de Bruijn indices or a logical audit. No second
Lean CLI or structural AST helper ran. Rendering cannot establish proof identity,
metadata equality to published source, typing or a trusted dependency closure.

NEW observation: actual Calls variant52 (CURRENT:INCREMENTAL:Query31SourceCalls:part0)
has18,236 type characters and98,761,710 value characters. Its complete type ends
with length8, stateChain and materializedOutputs, without the first-state anchor.
Actual Bridge variant84 (CURRENT:INCREMENTAL:Query31SourceOracleBridge:part0) has
22,303 type characters and575,135 value characters. Its complete type contains
that anchor. The actual Bridge value names Calls at character53809, and binds
hfirst at440469; its enclosing Exists.casesOn predicate also requires the anchor.
This independently supplies actual rendering evidence for the REUSED358 mismatch;
it is not a new normally checked replay of that mismatch.

The following complete statements use readable published notation for the actual
weaker type and the proposed stronger type. The full exact actual type rendering
is retained separately. This changes no premise, carrier, quantifier or outcome.

BEFORE: actual361 weaker type rendered in readable published notation:

```lean
theorem queries_success_with_digest_pairs_full {H : Type} (B : QueriesModel.Boundaries)
    (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (out : Array U32 22#usize)
    (h : QueriesModel.queries B D self row payload = ok (.Ok out,after)) :
    ∃ absorbed blocks advances selected,
      ∃ pairs : List (DigestPair D absorbed.hash),
        transcript.Transcript.absorb D self row payload = ok absorbed ∧
        B.decode blocks advances = ok (.Ok (out,selected)) ∧
        after = {absorbed with state := selected} ∧
        pairs.length = 8 ∧
        stateChain pairs ∧ materializedOutputs pairs blocks advances
```

AFTER: proposed stronger conclusion only:

```lean
theorem queries_success_with_digest_pairs_full {H : Type} (B : QueriesModel.Boundaries)
    (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (out : Array U32 22#usize)
    (h : QueriesModel.queries B D self row payload = ok (.Ok out,after)) :
    ∃ absorbed blocks advances selected,
      ∃ pairs : List (DigestPair D absorbed.hash),
        transcript.Transcript.absorb D self row payload = ok absorbed ∧
        B.decode blocks advances = ok (.Ok (out,selected)) ∧
        after = {absorbed with state := selected} ∧
        pairs.length = 8 ∧
        (∃ first rest, pairs = first :: rest ∧ first.state = absorbed.state) ∧
        stateChain pairs ∧ materializedOutputs pairs blocks advances
```

No premise/binder/carrier/outcome changes. H/B/D/self/after/row/payload/out/h
and every old absorb/decode/after/length/stateChain/materializedOutputs conjunct
are unchanged. The addition is solely the initial pair anchor conclusion.
Do not derive it from arbitrary list length/stateChain, introduce a new premise,
weaken Bridge, or use proof irrelevance between different propositions.

## Concrete actual-value repair sites

Actual Calls has one `fun (self1` at506471; hcall1's binder at1009136 explicitly
states absorb D self row payload = ok self1. Pair0's unique let at95895428
constructs DigestPair.mk with state `Transcript.state H self1`. Pair1..pair7 each
have a unique let too. The unique pairs let at95951146 contains exactly eight
List.cons applications with pair0..pair7 followed by List.nil (complete let is
in inspection361.json). Thus the concrete witness is present in the actual
rendering, rather than inferred from length or stateChain.

Preserve the existing output Exists.intro predicates/witnesses beginning at
95848078 (absorbed),95862011 (blocks),95875793 (advances),95886934 (selected), and
98684685 (pairs). These are not a contiguous final text block: pair lets and the
materialized-output argument occur between them. Do not mistake the unrelated
Exists.intro at73279954 for the absorbed witness; its carrier is a product.

At98691806 the final pairs witness is followed by And.intro; the existing proof
arguments are hcall1 (98698632), hdecode (98705208), ha, length reflexivity, the
stateChain proof, and hmaterial (98755382). The old innermost And.intro begins
at98706605. Preserve all these existing proofs. In the same concrete context,
insert after length the finite witness

```lean
⟨pair0, [pair1, pair2, pair3, pair4, pair5, pair6, pair7], rfl, rfl⟩
```

and make the tail `And.intro hfirst (And.intro hchain hmaterial)`, keeping the
existing chain/material proofs as hchain/hmaterial here (hchain is a descriptive
placeholder, not a new actual binder). The witness proposition is
`∃ first rest, pairs = first :: rest ∧ first.state = self1.state`. The supplied
state component follows the actual Pair0 constructor and the actual pairs let;
this is the proposed definitional equality, not an executed kernel check.

Strengthen the full result proposition at the declaration type, all five
output existential predicate arguments, and every enclosing elimination motive
whose result is that proposition, with the same anchor at the same dependent
absorbed/pairs scope. Calls' rendering contains157 textual Exists.casesOn,
155 And.casesOn,155 bind_success and33 Eq.ndrec occurrences. Counts are NOT an
instruction to rewrite every occurrence: the success decomposition and unrelated
local/index proofs must remain intact. In particular, preserve hcall1's linkage
to self1, dependent hash arguments, selected/after equations, mark/trace binders,
and all scopes through their continuations. Retype the enclosing result motives
of the execution decompositions and relevant equality transports; leave unrelated
materialized-output existence and finite-index proofs unchanged. A bottom-tail
patch alone leaves stale result predicates and is not sufficient.

Published source is reference only: its explicit finite eight-pair proof and
first-state witness match this intended construction shape. No source-text to
actual-proof identity claim follows. Implementing/validating an Expr rewrite,
checking the stronger theorem, and rechecking the unchanged dependent Bridge
require later lead allocation. None was attempted. No generic wrapper, theorem
projection, additional equality/input-retention premise or proof irrelevance
between different propositions supplies the missing anchor.

## Retained assumptions and independent obstruction

Complete hidden-type renderings include Boundaries.mk/decode/embed, DigestCall.mk,
DigestPair.mk, stateChain and materializedOutputs. Boundaries retains arbitrary
decode and embed callbacks, not a new output-equivalence premise. DigestCall
retains exact source slice/tag/input/digest equations; DigestPair retains shared
state/tag equations. StateChain constrains adjacent pairs only; materializedOutputs
retains indexed array readbacks. Neither yields the initial state anchor alone.
The proposed conclusion must come from successful source execution h, with B,
D and all original binders unchanged. No assumption is discharged or added here;
external SDK/std/runtime/allocator/extraction semantics are not audited by raw IO.

The independent REUSED358 private-name elaborator-metadata collision remains
open. Raw IO avoids logical insertion and therefore does not repair or test it.
No metadata adapter, normal kernel insertion, setEnv, proof transformation,
trust import, renamed private constant or alternate selection policy was used.
Only88 scoped names were exported; no alternate origin was searched or ruled out.
Next deliverable: lead-approved construction of a normally checked strengthened
Calls theorem in a coherent exact-name context, followed by the unchanged Bridge
and an actual standard-axiom/dependency audit. No whole replay without allocation.
Both security targets remain NOT ESTABLISHED; all SDK/std/runtime/allocator/
extraction/child/history/event/mark/P2Prime/native/artifact boundaries remain.
