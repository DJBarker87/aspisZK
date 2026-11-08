import NNX_PartitionFinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_LeafShape
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical MultiproofConeSlices

theorem parts (tag : U8) (value salt : Slice U8)
 (saltLength : salt.val.length=32) (valueLength : value.val.length=128 ∨ value.val.length=480) :
 LIBC_HashPartitions.Shape (NNC_ResumeEvents.parts (Port4B_LeafCode.parts tag value salt)) := by
 refine ⟨_,_,_,rfl,?_,Or.inr ⟨?_,?_⟩⟩
 · simpa only [NNC_ByteCarriers.host,List.length_map] using saltLength
 · rfl
 · simpa only [NNC_ByteCarriers.host,List.length_map] using valueLength

theorem source (kind : Usize) (opening : Slice U8) (length : opening.val.length=832) :
 LIBC_HashPartitions.Shape (NNC_ResumeEvents.parts (Port4B_LeafCode.input kind opening)) := by
 unfold Port4B_LeafCode.input
 split
 · apply parts
   · simp [sub,length]
   · exact Or.inr (by simp [sub,length])
 · split
   · apply parts
     · simp [sub,length]
     · exact Or.inl (by simp [sub,length])
   · apply parts
     · simp [sub,length]
     · exact Or.inl (by simp [sub,length])
#print axioms parts
#print axioms source
end AspisR1.NNX_LeafShape
end
