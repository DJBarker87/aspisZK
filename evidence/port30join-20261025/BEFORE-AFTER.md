# Exact proposed obligation and quantified change

Status: proposal only; no Lean invocation. Complete before statement/body:
`sources/904745b496-S2W_D189Consolidation.lean.txt:accepted_run`.
Complete after statement/body: `tools/port30join-20261025/Port30JOIN_Composed.lean`.
Complete SDK/S1 statements and hidden SourceCuts/FirstCut/SecondCut are captured
in sources, pinned in source-pins.json. No existing statement was changed.

Before, schematically (read full source for the actual binders):

```
accepted_run L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
  adapterOps native1 native2 hashv extraction sha256 H p1 syscall
  program data1 data2 slot state1 state2 final1 final2 saved post1 post2
  accepted1 accepted2 port firstMarks secondMarks :
  exists f s outer pre middle fs ss,
    SourceCuts ... f s /\ expanded /\ ownedFrame /\ layout /\ unchanged /\
    nativeBefore1 /\ nativeBefore2 /\
    forall decode nodes y1, writer(f.semantic,f.pub,f.proof,f.split) ->
      reader -> protectedVersion -> P2Prime -> entry -> multiproof -> scan ->
      exists parsed, S2CallerFacts(actual observation f s ...) /\ reachedSites
```

After, exact proposed theorem `Port30JOIN.accepted_original_sdk_s2_s1` fixes the
SAME ops to the existing concrete SDK/values/round/B installation. First
acceptance is the actual `originalFirst native1 copy allocator e ...` equation;
`first_eq_original` derives the wrapper equation in this chosen definition
context. Second acceptance is the same second wrapper, no new native law.
Added parameters are existing S1 Ops/B and p/root/length trace interpretation,
not a caller-output certificate. All runtime/child/mark hypotheses remain.
The conclusion is:

```
checkpointWrite /\ fullNativePublicFrame /\
exists rawCut f s selectedPublic outer pre middle fs ss,
  SourceCuts ... rawCut s /\ f = {rawCut with semantic := selectedPublic} /\
  semantic_public rawCut.statement = ok selectedPublic /\ SourceCuts ... f s /\
  completeDecodeEncodeFirstReuse(f) /\ completeS1NumericPrepareClaimJointTrace(f) /\
  [same expanded/owned/layout/unchanged/nativeBefore results] /\
  forall decode nodes y1, writer(f.semantic,f.pub,f.proof,f.split) ->
    [same reader/protectedVersion/P2Prime/entry/multiproof/scan boundaries] ->
    exists parsed, [same full S2CallerFacts and reachedSites]
```

Every field except semantic is definitionally identical, including BOTH account
handles, raw/public/proof slices, statement and split. SecondCut and returned
saved/post/final tuple are unchanged. SDK output relates that SAME f.pub to the
original buffer, 1880 length, native SDK data-cell bytes, actual/nominal decoding
and full encoding; S1 receives the SAME f.pub/f.proof/f.statement/f.split.
Its complete existential zero/semantic/y1/view/sem/prepared/scratch package is
written out: original prepare, same gamma scratch/borrowed claim, canonical
powers/gamma/kappa, returned challenge/alpha/extra/before_z1 ranges, exact joint
serialized trace/row31 meaning, and same checkpoint continuation.

This is a visible existential selection and installation specialization, not
universal identity for rawCut.semantic, premise removal, native semantics or an
adaptive experiment law. Conditional writer now refers to the selected semantic;
it is NOT inferred from a writer theorem at arbitrary rawCut.semantic. The proof
rebuilds input_schedule from chosen.first, chosen.second and the existing named
child ports. It reuses concrete D189 accepted_run's witnesses/trace/frames; it
never matches unrelated SDK/S2 existential witnesses and adds no equality,
retention, FullForest, output-equivalence or whole-caller input premise.

`originalFirst` itself embeds the old cached wrapper body with one old match_2
helper substituted, then checked under the factored dependency context. Its
ordinary first_eq_original proof is valid reused scoped evidence. Rechecking the
old accepted_run proof in that chosen current context would be a NEW RE-PIN,
not literal original closure. All13 computational conflicts remain explicit.
