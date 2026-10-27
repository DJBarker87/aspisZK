import R1Z.ProverRw19MathematicalAssembly
import R1Z.ProverRw19ByteLength
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19MathematicalLength
open Aeneas Aeneas.Std Result

theorem proof (fields : ProverCommitFront46.Fields)
    (queries : List ProverCommitPublish43.QueryParts)
    (slots : List ProverCommitPublish43.Slot) :
    ProverRw19ByteLength.HasLength 57607
      (ProverRw19MathematicalAssembly.proofBytes fields queries slots) := by
  unfold ProverRw19MathematicalAssembly.proofBytes
  split
  · trivial
  · rename_i result success
    change (result.map ProverRw19MathematicalAssembly.byte).length = 57607
    rw [List.length_map]
    exact ProverRw19AssemblyLength.reference fields queries slots result success

#print axioms proof
end R1Z.ProverRw19MathematicalLength
