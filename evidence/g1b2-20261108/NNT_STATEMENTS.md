# Full before/after consumer statements
Only the authorised structure/premise edits and unused nmn removal apply. NMF and case-split structures have their full unchanged fields re-expressed over the new G1a carrier in NNT_TopL. No adversary, carrier, event or conclusion is specialised.

## NNT_TopLCore.stage1Root
Before (`evidence/top-assembly-20261107/TAS_Top.lean`):
```lean
theorem stage1Root (nmo : NMO_Root L V0 VL I) (nmp : NMP_Roots L V0 VL P I)
    (nmt : NMT_Roots L V0 VL P C I) (nmv : NMV_Roots L D V0 VL P C I) :
    TX1_344.RowSpec_344 VL P C I.f344
```
After:
```lean
theorem stage1Root (nmo : NMO_Root L V0 VL I) (nmp : NMP_Roots L V0 VL P I)
    (nmt : NMT_Roots L V0 VL P C I) (nmv : NMV_Roots L D V0 VL P C I) :
    TX1_344.RowSpec_344 VL P C I.f344
```

## NNT_TopLCore.validateRoot
Before (`evidence/top-assembly-20261107/TAS_Top.lean`):
```lean
theorem validateRoot (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I)
    (nms : NMS_Roots L D V0 VL I) : TX2_242.RowSpec_242 L D I.f242
```
After:
```lean
theorem validateRoot (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I)
    (nms : NMS_RootsL L D V0 VL I) : TX2_242.RowSpec_242 L D I.f242
```

## NNT_TopLCore.entryRoot
Before (`evidence/top-assembly-20261107/TAS_Top.lean`):
```lean
theorem entryRoot (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I)
    (nms : NMS_Roots L D V0 VL I) (nmv : NMV_Roots L D V0 VL P C I)
    (nmw : NMW_Roots L D V0 VL P C I) (nmt : NMT_Roots L V0 VL P C I)
    (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit))
    (h : Refines064 V0 I.f064 R0 w) :
    TX1_330.RowSpec_330 L D (lib V0 R0 w) VL P C I.entry
```
After:
```lean
theorem entryRoot (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I)
    (nms : NMS_RootsL L D V0 VL I) (nmv : NMV_Roots L D V0 VL P C I)
    (nmw : NMW_Roots L D V0 VL P C I) (nmt : NMT_Roots L V0 VL P C I)
    (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit))
    (h : LawRefines V0 R0 w) :
    TX1_330.RowSpec_330 L D (lib V0 R0 w) VL P C I.entry
```

## NNT_TopLCore.row333_is_221
Before (`evidence/top-assembly-20261107/TAS_Top.lean`):
```lean
theorem row333_is_221 (V : V2Lib) :
    TX1_333.RowSpec_333 L D V VL P C I.process =
      TX2_221.RowSpec_221 L D V (TX1_344.asStage1 VL P C) I.process
```
After:
```lean
theorem row333_is_221 (V : V2Lib) :
    TX1_333.RowSpec_333 L D V VL P C I.process =
      TX2_221.RowSpec_221 L D V (TX1_344.asStage1 VL P C) I.process
```

## NNT_TopLCore.row330_is_213
Before (`evidence/top-assembly-20261107/TAS_Top.lean`):
```lean
theorem row330_is_213 (V : V2Lib) :
    TX1_330.RowSpec_330 L D V VL P C I.entry =
      TX2_213.RowSpec_213 L D V (TX1_344.asStage1 VL P C) I.entry
```
After:
```lean
theorem row330_is_213 (V : V2Lib) :
    TX1_330.RowSpec_330 L D V VL P C I.entry =
      TX2_213.RowSpec_213 L D V (TX1_344.asStage1 VL P C) I.entry
```

## NNT_TopLCore.weakEntry
Before (`evidence/top-assembly-20261107/TAS_Top.lean`):
```lean
theorem weakEntry (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I)
    (nms : NMS_Roots L D V0 VL I) (nmv : NMV_Roots L D V0 VL P C I)
    (nmw : NMW_Roots L D V0 VL P C I) (nmt : NMT_Roots L V0 VL P C I)
    (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    {S : Sig} (g : NNC_G1a S L V0 VL I) :
    ∀ a s env, TX2_213.Ref L D (lib V0 (fun _ _ => True) g.w) (TX1_344.asStage1 VL P C)
      a s env (I.entry a s env)
```
After:
```lean
theorem weakEntry (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I)
    (nms : NMS_RootsL L D V0 VL I) (nmv : NMV_Roots L D V0 VL P C I)
    (nmw : NMW_Roots L D V0 VL P C I) (nmt : NMT_Roots L V0 VL P C I)
    (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    {S : Sig} (g : NNC_G1aL S L V0 VL I) :
    ∀ a s env, TX2_213.Ref L D (lib V0 (fun _ _ => True) g.w) (TX1_344.asStage1 VL P C)
      a s env (I.entry a s env)
```

## NNT_TopLCore.canonicalRef240
Before (`evidence/top-assembly-20261107/TAS_Top.lean`):
```lean
theorem canonicalRef240 (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I)
    (nms : NMS_Roots L D V0 VL I) (nmv : NMV_Roots L D V0 VL P C I)
    (nmw : NMW_Roots L D V0 VL P C I) (nmt : NMT_Roots L V0 VL P C I)
    (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I) (nmn : NMN_Root L V0 VL I)
    (a : TX2_213.Args) (s : SdkState) (env : Env) (hq : ASQ8 a.data)
    (dom : TX2_240.Domain V0 a s) :
    TX2_240.Ref L D V0 a s env (I.entry a s env)
```
After:
```lean
theorem canonicalRef240 (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I)
    (nms : NMS_RootsL L D V0 VL I) (nmv : NMV_Roots L D V0 VL P C I)
    (nmw : NMW_Roots L D V0 VL P C I) (nmt : NMT_Roots L V0 VL P C I)
    (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (a : TX2_213.Args) (s : SdkState) (env : Env) (hq : ASQ8 a.data)
    (dom : TX2_240.Domain V0 a s) :
    TX2_240.Ref L D V0 a s env (I.entry a s env)
```

## NNT_TopLCore.asq8Frame
Before (`evidence/top-assembly-20261107/TAS_Top.lean`):
```lean
theorem asq8Frame (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I)
    (nms : NMS_Roots L D V0 VL I) (nmv : NMV_Roots L D V0 VL P C I)
    (nmw : NMW_Roots L D V0 VL P C I) (nmt : NMT_Roots L V0 VL P C I)
    (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    {S : Sig} (g : NNC_G1a S L V0 VL I) :
    ∀ a s env, ASQ8 a.data → Frame s (I.entry a s env)
```
After:
```lean
theorem asq8Frame (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I)
    (nms : NMS_RootsL L D V0 VL I) (nmv : NMV_Roots L D V0 VL P C I)
    (nmw : NMW_Roots L D V0 VL P C I) (nmt : NMT_Roots L V0 VL P C I)
    (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    {S : Sig} (g : NNC_G1aL S L V0 VL I) :
    ∀ a s env, ASQ8 a.data → Frame s (I.entry a s env)
```

## NNT_TopLCore.domain240_of_rep
Before (`evidence/top-assembly-20261107/TAS_Top.lean`):
```lean
theorem domain240_of_rep {S : Sig} (r0 : NNC_R0Rep S V0) (c : S.Ctx) (h : S.Root0Native c) :
    TX2_240.Domain V0 (S.args2 c) (S.state2 c)
```
After:
```lean
theorem domain240_of_rep {S : Sig} (r0 : NNC_R0Rep S V0) (c : S.Ctx) (h : S.Root0Native c) :
    TX2_240.Domain V0 (S.args2 c) (S.state2 c)
```

## NNT_TopLCore.top
Before (`evidence/top-assembly-20261107/TAS_Top.lean`):
```lean
theorem top (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    -- existing headline (no job)
    (hl : Headline S)
    -- A0 (G0 job)
    (a0 : A0_Digest S)
    -- row roots, RSL form
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    -- NNC_
    (g1a : NNC_G1a S L V0 VL I) (nmf : NNC_NMFPrime S L D V0 VL P C I g1a)
    (cs : NNC_CaseSplit S L D V0 VL P C I nmf) (r0 : NNC_R0Rep S V0)
    -- NND_
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    -- NNE_
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    -- the deployed pair: headline binders retained, plus the actual run
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      (S.Concl c (S.model1 c) (S.model2 c) ∨ S.Event c (S.model1 c))
```
After:
```lean
theorem top (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    -- existing headline (no job)
    (hl : Headline S)
    -- A0 (G0 job)
    (a0 : A0_Digest S)
    -- row roots, RSL form
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_RootsL L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
   
    -- NNC_
    (g1a : NNC_G1aL S L V0 VL I) (nmf : NNC_NMFPrime S L D V0 VL P C I g1a)
    (cs : NNC_CaseSplit S L D V0 VL P C I nmf) (r0 : NNC_R0Rep S V0)
    -- NND_
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    -- NNE_
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    -- the deployed pair: headline binders retained, plus the actual run
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      (S.Concl c (S.model1 c) (S.model2 c) ∨ S.Event c (S.model1 c))
```

## NNT_TopLEvent.event_top_splitB
Before (`evidence/event-b-20261107/EVB_EventB.lean`):
```lean
theorem top_splitB (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (R : RecSig S) (rs : RecSelect S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (realizes : R.Realizes c)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      sp.Rest c (S.model1 c) (S.model2 c) ∧
      (sp.Outcome c (S.model1 c) (S.model2 c) ∨ R.EventRec c)
```
After:
```lean
theorem event_top_splitB (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_RootsL L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
   
    (g1a : NNC_G1aL S L V0 VL I) (R : RecSig S) (rs : RecSelect S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (realizes : R.Realizes c)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      sp.Rest c (S.model1 c) (S.model2 c) ∧
      (sp.Outcome c (S.model1 c) (S.model2 c) ∨ R.EventRec c)
```

## NNT_TopLEvent.event_top_splitB_full
Before (`evidence/event-b-20261107/EVB_EventB.lean`):
```lean
theorem top_splitB_full (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (R : RecSig S) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (realizes : R.Realizes c)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      sp.Rest c (S.model1 c) (S.model2 c) ∧
      (hb.OutcomeRec c (S.model1 c) (S.model2 c) ∨ R.EventRec c)
```
After:
```lean
theorem event_top_splitB_full (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_RootsL L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
   
    (g1a : NNC_G1aL S L V0 VL I) (R : RecSig S) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (realizes : R.Realizes c)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      sp.Rest c (S.model1 c) (S.model2 c) ∧
      (hb.OutcomeRec c (S.model1 c) (S.model2 c) ∨ R.EventRec c)
```

## NNT_TopLB.top_splitB
Before (`evidence/top-assembly-20261107/TAS_TopB.lean`):
```lean
theorem top_splitB (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle)
    (queries : X.QueriesF fx) (run : Runs S I (ctxB X fx w H)) :
    S.Bound (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      sp.Rest (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      (hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∨
        X.ERec fx H)
```
After:
```lean
theorem top_splitB (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_RootsL L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
   
    (g1a : NNC_G1aL S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle)
    (queries : X.QueriesF fx) (run : Runs S I (ctxB X fx w H)) :
    S.Bound (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      sp.Rest (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      (hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∨
        X.ERec fx H)
```

## NNT_TopLB.fail_sub_rec
Before (`evidence/top-assembly-20261107/TAS_TopB.lean`):
```lean
theorem fail_sub_rec (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle) (queries : X.QueriesF fx)
    (fail : Runs S I (ctxB X fx w H) ∧
      ¬ hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H))) :
    X.ERec fx H
```
After:
```lean
theorem fail_sub_rec (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_RootsL L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
   
    (g1a : NNC_G1aL S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle) (queries : X.QueriesF fx)
    (fail : Runs S I (ctxB X fx w H) ∧
      ¬ hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H))) :
    X.ERec fx H
```

## NNT_TopLB.deployed_charge
Before (`evidence/top-assembly-20261107/TAS_TopB.lean`):
```lean
theorem deployed_charge (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (X : ExecB S R) (Ex : Expect X.Oracle) (fx : X.Fixed) (wOf : X.Oracle → X.World)
    (queries : X.QueriesF fx)
    (r m : X.Oracle → Rat) (T : Rat)
    (hm : ∀ H, 0 ≤ m H)
    (each : ∀ H, r H ≤ m H + ind (X.ERec fx H))
    (budget : Ex.E m + Ex.E (fun H => ind (X.ERec fx H)) ≤ T) :
    Ex.E (fun H => max (r H)
      (ind (Runs S I (ctxB X fx (wOf H) H) ∧
        ¬ hb.OutcomeRec (ctxB X fx (wOf H) H) (S.model1 (ctxB X fx (wOf H) H))
          (S.model2 (ctxB X fx (wOf H) H))))) ≤ T
```
After:
```lean
theorem deployed_charge (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_RootsL L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
   
    (g1a : NNC_G1aL S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (X : ExecB S R) (Ex : Expect X.Oracle) (fx : X.Fixed) (wOf : X.Oracle → X.World)
    (queries : X.QueriesF fx)
    (r m : X.Oracle → Rat) (T : Rat)
    (hm : ∀ H, 0 ≤ m H)
    (each : ∀ H, r H ≤ m H + ind (X.ERec fx H))
    (budget : Ex.E m + Ex.E (fun H => ind (X.ERec fx H)) ≤ T) :
    Ex.E (fun H => max (r H)
      (ind (Runs S I (ctxB X fx (wOf H) H) ∧
        ¬ hb.OutcomeRec (ctxB X fx (wOf H) H) (S.model1 (ctxB X fx (wOf H) H))
          (S.model2 (ctxB X fx (wOf H) H))))) ≤ T
```

## NNT_TopL.top_splitB_counts
Before (`evidence/top-assembly-20261107/TAS_TopB_NNE.lean`):
```lean
theorem top_splitB_counts (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (R : RecSig S) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (realizes : R.Realizes c)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (count1 : (S.args1 c).accounts.length = 3)
    (count2 : (S.args2 c).accounts.length = 7)
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      sp.Rest c (S.model1 c) (S.model2 c) ∧
      (hb.OutcomeRec c (S.model1 c) (S.model2 c) ∨ R.EventRec c)
```
After:
```lean
theorem top_splitB_counts (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_RootsL L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
   
    (g1a : NNC_G1aL S L V0 VL I) (R : RecSig S) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (realizes : R.Realizes c)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (count1 : (S.args1 c).accounts.length = 3)
    (count2 : (S.args2 c).accounts.length = 7)
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      sp.Rest c (S.model1 c) (S.model2 c) ∧
      (hb.OutcomeRec c (S.model1 c) (S.model2 c) ∨ R.EventRec c)
```

## NNT_TopL.top_splitB_physical
Before (`evidence/top-assembly-20261107/TAS_TopB_NNE.lean`):
```lean
theorem top_splitB_physical {S : Sig} {R : RecSig S}
    (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (count1 : ∀ c, (S.args1 c).accounts.length = 3)
    (count2 : ∀ c, (S.args2 c).accounts.length = 7)
    (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle)
    (queries : X.QueriesF fx) (run : Runs S I (ctxB X fx w H)) :
    S.Bound (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      sp.Rest (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      (hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∨
        X.ERec fx H)
```
After:
```lean
theorem top_splitB_physical {S : Sig} {R : RecSig S}
    (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_RootsL L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
   
    (g1a : NNC_G1aL S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (count1 : ∀ c, (S.args1 c).accounts.length = 3)
    (count2 : ∀ c, (S.args2 c).accounts.length = 7)
    (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle)
    (queries : X.QueriesF fx) (run : Runs S I (ctxB X fx w H)) :
    S.Bound (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      sp.Rest (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      (hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∨
        X.ERec fx H)
```

## NNT_TopL.selected_top_split
Before (`evidence/phys-adapter-20261111/NNE_TopSplit.lean`):
```lean
theorem top_split (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (nmf : NNC_NMFPrime S L D V0 VL P C I g1a)
    (cs : NNC_CaseSplit S L D V0 VL P C I nmf) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (count1 : (S.args1 c).accounts.length = 3)
    (count2 : (S.args2 c).accounts.length = 7)
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      sp.Rest c (S.model1 c) (S.model2 c) ∧
      (sp.Outcome c (S.model1 c) (S.model2 c) ∨ S.Event c (S.model1 c))
```
After:
```lean
theorem selected_top_split (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_RootsL L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
   
    (g1a : NNC_G1aL S L V0 VL I) (nmf : NNC_NMFPrime S L D V0 VL P C I g1a)
    (cs : NNC_CaseSplit S L D V0 VL P C I nmf) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (count1 : (S.args1 c).accounts.length = 3)
    (count2 : (S.args2 c).accounts.length = 7)
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      sp.Rest c (S.model1 c) (S.model2 c) ∧
      (sp.Outcome c (S.model1 c) (S.model2 c) ∨ S.Event c (S.model1 c))
```
