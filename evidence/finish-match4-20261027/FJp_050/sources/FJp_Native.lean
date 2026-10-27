import FIs_Native
set_option autoImplicit false
namespace AspisR1.FJp_Native
open Aeneas Aeneas.Std Result
/-- The existing native witness, with its actual powers constructor retained. -/
def Calls {F CoreError Hash : Type} (base : VTop_Stages.Ops)
    (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (t : Cons_Native.Witness) : Prop :=
  FIs_Native.Calls base finishOps reserved queryOps geoOps D hash pub proof checkpoint t ∧
  Tx2N_Powers.powers 29#usize t.p2.gamma=ok t.g2
end AspisR1.FJp_Native
