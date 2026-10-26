import SdkC_Oracle
import MultiproofConePhysicalTransport
set_option autoImplicit false
namespace AspisR1.F3N_PhysicalCode
open Aeneas Aeneas.Std Result
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConePhysicalProgram MultiproofConePhysicalTransport

def lower {A : Type} : SdkC_Source.Code A → Run A
  | .done a=>.done (ok a)
  | .step r next=>checked r (fun x=>lower (next x))
  | .read parts next=>.ask parts (fun digest=>lower (next digest))

theorem transport {A : Type} (c : SdkC_Source.Code A) :
    MultiproofConePhysicalTransport.transport (lower c)=SdkC_Oracle.program c := by
  induction c with
  | done a=>rfl
  | step r next ih=>cases r <;> simp only [lower,checked,MultiproofConePhysicalTransport.transport,SdkC_Oracle.program,ih]
  | read parts next ih=>
    simp only [lower,MultiproofConePhysicalTransport.transport,SdkC_Oracle.program]
    congr 1
    funext answer
    exact ih _

theorem bind {A B : Type} (c : SdkC_Source.Code A) (next : A → SdkC_Source.Code B) :
    lower (CheckpointBytes5Effect.bind c next)=AspisV8R19.OracleProgramOps.bind (lower c) (fun r=>match r with
      | ok a=>lower (next a) | fail e=>.done (fail e) | div=>.done div) := by
  induction c with
  | done a=>rfl
  | step r k ih=>cases r <;> simp only [CheckpointBytes5Effect.bind,lower,checked,ih,AspisV8R19.OracleProgramOps.bind]
  | read parts k ih=>
    simp only [CheckpointBytes5Effect.bind,lower,AspisV8R19.OracleProgramOps.bind]
    congr 1
    funext answer
    exact ih _

#print axioms transport
#print axioms bind
end AspisR1.F3N_PhysicalCode
