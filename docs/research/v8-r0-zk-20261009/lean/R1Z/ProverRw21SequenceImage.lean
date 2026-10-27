import R1Z.ProverRw21FlatSequence
import R1Z.ProverRw21WideImage
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21SequenceImage
open Aeneas Aeneas.Std ProverRw21WideCarrier

theorem image (xs : List W) (h : ∀ x∈xs,canonical x) :
    (ProverRw21FlatSequence.bytes xs).map ProverRw21ByteCarrier.decode =
      xs.flatMap (fun x => ProverRw21ProtocolOutput.wide (value x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [ProverRw21FlatSequence.bytes] at ih
    simp only [ProverRw21FlatSequence.bytes,List.flatMap_cons,List.map_append]
    rw [ProverRw21WideImage.mathematical_image x (h x (by simp)),
      ih (fun y hy => h y (by simp only [List.mem_cons];exact Or.inr hy))]

theorem encoded (xs : List E) :
    ProverRw21FlatSequence.bytes (xs.map encode) =
      (xs.flatMap ProverRw21ProtocolOutput.wide).map ProverRw19MathematicalAssembly.byte := by
  apply ProverRw21ByteCarrier.decode_list_injective
  rw [ProverRw21ByteCarrier.decode_encode_list,
    image (xs.map encode) (by
      intro x hx
      rcases List.mem_map.mp hx with ⟨y,hy,rfl⟩
      exact canonical_encode y)]
  simp only [List.flatMap_map,value_encode]

#print axioms image
#print axioms encoded
end R1Z.ProverRw21SequenceImage
