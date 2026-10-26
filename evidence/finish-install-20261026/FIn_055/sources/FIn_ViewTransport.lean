import Cons_Native
import T2Nat_FinishResult
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIn_ViewTransport
open Aeneas Aeneas.Std Result AspisR1Stage2

/-- Calls retains no byte-read provenance for v2: any separately successful
view can replace it without changing the other native observations. This is an
interface statement, not a claim that the source executes that replacement. -/
theorem calls {W C Hash : Type} (base : VTop_Stages.Ops) (finish : Stage2Finish.FinishOps W)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (t : Cons_Native.Witness)
    (old : Cons_Native.Calls base finish reserved query geo D hash pub proof checkpoint t)
    (v : verifier.View)
    (success : Port4D_FinishInstall.finish finish v t.p2
      {t.returned2 with weights:=t.back2 t.flushed2} none=ok (.Ok ())) :
    Cons_Native.Calls base finish reserved query geo D hash pub proof checkpoint {t with v2:=v} := by
  obtain ⟨reader,native,length,allocation,logs,queryCall,back,flush,op19,returned,effects⟩ := old
  refine ⟨reader,native,length,allocation,logs,queryCall,back,flush,success,success,?_⟩
  intro Hash' D' hash' before
  exact T2Nat_FinishResult.accepted_effects D' hash' finish v t.p2
    {t.returned2 with weights:=t.back2 t.flushed2} success before

#print axioms calls
end AspisR1.FIn_ViewTransport
end
