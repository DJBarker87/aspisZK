import F3N_PhysicalCode
set_option autoImplicit false
namespace AspisR1.F3N_PhysicalBind
open Aeneas Aeneas.Std Result
open AspisV8R19.MemoizedProgramLaw
open F3N_PhysicalCode

theorem bind {A B : Type} (c : SdkC_Source.Code A) (next : A → SdkC_Source.Code B) :
    lower (c >>= next)=AspisV8R19.OracleProgramOps.bind (lower c) (fun r=>match r with
      | ok a=>lower (next a) | fail e=>.done (fail e) | div=>.done div) := by
  exact F3N_PhysicalCode.bind c next

theorem pure {A : Type} (a : A) : lower (Pure.pure a : SdkC_Source.Code A)=Program.done (ok a) := rfl

#print axioms bind
#print axioms pure
end AspisR1.F3N_PhysicalBind
