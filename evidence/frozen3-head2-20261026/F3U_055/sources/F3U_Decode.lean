import DrvC_NativeDecode
import RawJ_RecordCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_Decode
open Aeneas Aeneas.Std Result
open DrvC_Installation S2W_NativeConsolidation

theorem same {F C : Type} (c : Configuration F C)
    (program : S2W_ExtractionBoundary.Program)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (data : Slice U8)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut) (log : S2W_Trace.Log)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned (sdk c) program accounts1 data=ok (.Ok saved))
    (cuts : SourceCuts (sdk c) accounts1 accounts2 saved f s)
    (recorded : RawJ_RecordCuts.Recorded f s saved log) :
    Port1_Driver.decodeSemantic (sdk c) f.pub=ok (some f.semantic) := by
  obtain ⟨pa,pu,pub,raw,stmt,semantic,proof,split,hpa,hpu,hraw,hpub,hd,hvalid,hsem,range,first,len⟩ :=
    DrvC_NativeDecode.first_call_decoded (sdk c) program accounts1 data saved accepted
  have pue : pu=f.publicAccount := Result.ok.inj (hpu.symm.trans cuts.public1Index)
  subst pu
  have pube : pub=f.pub := core.result.Result.Ok.inj (Result.ok.inj (hpub.symm.trans cuts.public1Read))
  subst pub
  have ste : stmt=f.statement := core.result.Result.Ok.inj (Result.ok.inj (hd.symm.trans cuts.decode))
  subst stmt
  have seme : semantic=f.semantic := Result.ok.inj (hsem.symm.trans recorded.1)
  subst semantic
  simp only [Port1_Driver.decodeSemantic,hd,hvalid,hsem,bind_tc_ok]

#print axioms same
end AspisR1.F3U_Decode
end
