import R1Z.ProverRw19AssemblyLength
import R1Z.ProverCommitFront46
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19AssemblyLength
open ProverCommitPublish43

theorem reference (fields : ProverCommitFront46.Fields) (ps : List QueryParts)
    (ss : List Slot) (result : Bytes)
    (success : ProverCommitFront46.referenceProof fields ps ss = .ok result) :
    result.length = 57607 :=
  assemble (ProverCommitFront46.referenceFront fields) ps ss 28359 57607 result success


#print axioms reference
end R1Z.ProverRw19AssemblyLength
