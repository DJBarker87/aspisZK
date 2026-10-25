# Proposed finite execution-tail repair — UNCOMPILED

Actual360 exports are unavailable: ordinary run_cmd failed before IO. These
complete before/after statements use immutable published notation and the
REUSED358 actual mismatch; they are NOT a new actual raw-type export. No
actual Expr positions/constructor spine were inspected. No theorem checked.

BEFORE: actual358 weaker statement reconstructed in published notation:

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

Proposed actual repair, contingent on an actual future value export: locate the
successful source execution's final five Exists.intro witnesses (absorbed,
blocks, advances, selected, pairs) and right-associated And.intro chain. Preserve
all preceding execution eliminations and old proof components. After length,
replace old And.intro hchain hmaterial with
And.intro (Exists.intro pair0 (Exists.intro [pair1,...,pair7]
  (And.intro rfl rfl))) (And.intro hchain hmaterial), using actual typed terms,
not this pseudocode. Corresponding predicate/type parameters and enclosing
eliminator motives must be strengthened throughout the same execution proof;
merely changing the outer introduction is insufficient when motives mention
its result. All original names, levels, binders and dependencies are retained.

Published source establishes the intended finite construction shape: self1
comes from the first successful absorb bind (hcall1); pair0.state is self1.state
by the displayed DigestPair constructor; pairs is [pair0,...,pair7]. Thus the
finite anchor witness is
`⟨pair0, [pair1,pair2,pair3,pair4,pair5,pair6,pair7], rfl, rfl⟩`.
Source-structural.json lists exact published line numbers, states, hcall fields
and execution bind decompositions. This does not certify the actual weaker
value has those lets or that the proposed term type-checks. No generic wrapper
over the weaker theorem supplies the missing fact.

The unchanged dependent Bridge retains H/M/Cv/L/B/D/p/pubInput/root/length/
self/after/row/payload/out/h, all original output conjuncts and oracle-address
conclusions. Its complete published statement/body is retained beside this
note. REUSED358 application diagnostic expects the anchor in the Calls result.
Actual Bridge TYPE/VALUE export and same-context normal check remain blocked.

Future SOURCE review alternative: remain entirely in Kernel.Environment,
replay normally checked exact-name declarations, build a new enclosing Expr /
Declaration, and normally check with Core.getMaxHeartbeats. Do not transport
kernel-only metadata into elaboration. No private constructors, manual records,
unchecked insertion, trust imports or rename/cast allowed. This is not executed.
