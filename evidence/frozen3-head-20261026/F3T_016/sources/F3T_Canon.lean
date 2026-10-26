import F3T_Bounds
import OraclePortStoredAdmissionC4
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Canon
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open F3T_Experiment

def canonInput (i : F3_Model.Input) : F3_Model.Input := {i with proof:=R16CanonReduction.proof i.proof}
def canon (P : Prover) : Prover := bind P fun i=>.done (canonInput i)

theorem canon_eval (P : Prover) (H : Bytes → State) :
    eval H (canon P)=((eval H P).1,canonInput (eval H P).2) := by
  simp only [canon,eval_bind,eval,List.append_nil]

theorem verifier_canon (D : LiteralByteProtocol.Decoder) (i : F3_Model.Input) :
    F3_Model.verifier D (canonInput i)=F3_Model.verifier D i := by
  exact OraclePortCanon.verifier_congr D (F3_Model.decision i.physical i.stored)
    i.semantic.value i.proof (R16CanonReduction.proof i.proof) (R16CanonReduction.erase_proof _)

theorem acceptance (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    (eval H (original D (canon P))).2.2=(eval H (original D P)).2.2 := by
  rw [original_eval,canon_eval,original_eval,verifier_canon]

theorem bound (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State,(eval H P).1.length≤Q) :
    ∀ H : Bytes → State,(eval H (canon P)).1.length≤Q := by
  intro H
  rw [canon_eval]
  exact hq H

#print axioms canon_eval
#print axioms verifier_canon
#print axioms acceptance
#print axioms bound
end AspisR1.F3T_Canon
end
