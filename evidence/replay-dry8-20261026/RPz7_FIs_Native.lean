import RPz7_SAG_NativeFull
set_option autoImplicit false
namespace AspisR1.FIs_Native
open Aeneas Aeneas.Std Result
open Cons_Native (Witness)
def Calls {F CoreError Hash : Type} (base : VTop_Stages.Ops)
    (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (t : Witness) : Prop :=
  Cons_Native.Calls base finishOps reserved queryOps geoOps D hash pub proof checkpoint t ∧
  Cons_NativeBuild.Aux reserved queryOps geoOps D hash pub proof checkpoint t ∧
  SAG_NativeFull.Shape (Tx2N_Execution.control (Tx2I_Install.stage (Op5T_Concrete.stage base) finishOps) reserved queryOps geoOps) proof t

end AspisR1.FIs_Native
