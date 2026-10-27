import RPz8_F3N_SameSecond
import F3N_FinishLog
import T2Nat_FinishResult
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_SecondFinish
open Aeneas Aeneas.Std Result

theorem from_calls {F C Hash : Type} (base : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (t : Cons_Native.Witness)
    (calls : Cons_Native.Calls base finish reserved query geo D hash pub proof checkpoint t)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (before : SdkC_Source.Log) :
    SdkC_Source.run hashv (T2Nat_Silent.code (T2Nat_FinishResult.installed finish t.v2 t.p2
      {t.returned2 with weights:=t.back2 t.flushed2})) before=(ok (.Ok ()),before) := by
  have accepted : Port4D_FinishInstall.finish finish t.v2 t.p2
      {t.returned2 with weights:=t.back2 t.flushed2} none=ok (.Ok ()) :=
    calls.2.2.2.2.2.2.2.2.2.1
  rw [F3N_FinishLog.silent,T2Nat_FinishResult.installed_erase,accepted]

#print axioms from_calls
end AspisR1.F3N_SecondFinish
end
