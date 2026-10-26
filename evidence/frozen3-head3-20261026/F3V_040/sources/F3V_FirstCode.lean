import F3V_LoweredPreparation
import F3U_FirstInstances
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_FirstCode
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode

theorem same (H : Bytes → State) (base : AspisR1CurrentCaller.Ops)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (physical proof : Slice U8) (split : Usize) :
    GExp_FirstCode.code base B std hashv D pub physical proof split=
      GExp_FirstCode.code base B std (F3U_Oracle.hashv H) (F3V_OracleDictionary.current H D) pub physical proof split := by
  simp only [F3U_FirstInstances.retained,F3U_FirstSkeleton.code]
  repeat' first
    | (solve | rfl)
    | (fail_if_no_progress rw [F3V_LoweredPreparation.same H D])
    | (apply congrArg (fun k => _ >>= k);funext x)
    | split

#print axioms same
end AspisR1.F3V_FirstCode
end
