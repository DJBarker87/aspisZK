import SdkC_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_IdealCode
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

theorem value {A Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (law : ∀ parts,D.digest hash parts=ok (MultiproofConePhysicalTransport.rawOracle H parts))
    (code : Code A) :
    (eval H (SdkC_Oracle.program code)).2=erase D hash code := by
  induction code with
  | done a=>rfl
  | step r k ih=>cases r <;> first | rfl | exact ih _
  | read parts k ih=>
    simp only [SdkC_Oracle.program,eval,erase,law,MultiproofConePhysicalTransport.rawOracle,bind_tc_ok]
    exact ih _

#print axioms value
end AspisR1.F3Q_IdealCode
end
