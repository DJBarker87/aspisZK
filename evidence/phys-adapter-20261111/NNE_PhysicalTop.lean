import NNE_TopSplit
set_option autoImplicit false
noncomputable section
namespace NNE_PhysicalTop
open RSL RSL.TAS RSL.TFM NNE_TopSplit
open RSL.TX2_241 (V2Lib)
open RSL.TX1_345 (S1Lib)
theorem physical_top_split (base : Sig) (d : NNE_AcceptanceSig.Data base)
    (r : NNE_RecordSig.Data base) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split (NNE_RecordSig.physical base d r)) (hl : Headline (NNE_RecordSig.physical base d r)) (a0 : A0_Digest (NNE_RecordSig.physical base d r))
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a (NNE_RecordSig.physical base d r) L V0 VL I) (nmf : NNC_NMFPrime (NNE_RecordSig.physical base d r) L D V0 VL P C I g1a)
    (cs : NNC_CaseSplit (NNE_RecordSig.physical base d r) L D V0 VL P C I nmf) (r0 : NNC_R0Rep (NNE_RecordSig.physical base d r) V0)
    (a1 : NND_A1 (NNE_RecordSig.physical base d r) VL P C) (a2 : NND_A2 (NNE_RecordSig.physical base d r) L D V0)
    (c : (NNE_RecordSig.physical base d r).Ctx) (hx : (NNE_RecordSig.physical base d r).Exhibited c) (queries : (NNE_RecordSig.physical base d r).Queries c ((NNE_RecordSig.physical base d r).model1 c))
    (frame : (NNE_RecordSig.physical base d r).GameFrame c) (trace : (NNE_RecordSig.physical base d r).TraceRep c I.entry)
    (ok1 : ∃ s', (I.entry ((NNE_RecordSig.physical base d r).args1 c) ((NNE_RecordSig.physical base d r).state1 c) ((NNE_RecordSig.physical base d r).env1 c)).exit = .ret (.ok (), s'))
    (out1 : (NNE_RecordSig.physical base d r).Out1 c (I.entry ((NNE_RecordSig.physical base d r).args1 c) ((NNE_RecordSig.physical base d r).state1 c) ((NNE_RecordSig.physical base d r).env1 c)))
    (ok2 : ∃ s', (I.entry ((NNE_RecordSig.physical base d r).args2 c) ((NNE_RecordSig.physical base d r).state2 c) ((NNE_RecordSig.physical base d r).env2 c)).exit = .ret (.ok (), s'))
    (out2 : (NNE_RecordSig.physical base d r).Out2 c (I.entry ((NNE_RecordSig.physical base d r).args2 c) ((NNE_RecordSig.physical base d r).state2 c) ((NNE_RecordSig.physical base d r).env2 c))) :
    (NNE_RecordSig.physical base d r).Bound c ((NNE_RecordSig.physical base d r).model1 c) ((NNE_RecordSig.physical base d r).model2 c) ∧
      sp.Rest c ((NNE_RecordSig.physical base d r).model1 c) ((NNE_RecordSig.physical base d r).model2 c) ∧
      (sp.Outcome c ((NNE_RecordSig.physical base d r).model1 c) ((NNE_RecordSig.physical base d r).model2 c) ∨ (NNE_RecordSig.physical base d r).Event c ((NNE_RecordSig.physical base d r).model1 c)) := by
 apply top_split (NNE_RecordSig.physical base d r) L D V0 VL P C I sp hl a0
   nmm nmx nms nmv nmw nmt nmp nmo nmn g1a nmf cs r0 a1 a2
   (NNE_RecordSig.a3 base d r VL P C) (NNE_RecordSig.a4 base d r L D V0)
   (NNE_RecordSig.a5 base d r L V0 VL P C I) c hx queries frame trace ok1 out1 ok2
 · exact NNE_EntryArgs.count _ 3 _ _
 · exact NNE_EntryArgs.count _ 7 _ _
 · exact out2

#print axioms physical_top_split
end NNE_PhysicalTop
end
