import RPz8_SCE_Experiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_SuffixShape
open AspisV8R19.DuplexFrames

/-- Accepted source suffix shape forces the 688-byte prefix to exist.
This is symbolic list-length arithmetic, not normalization of native bytes. -/
theorem prefix_exists (raw proof : Bytes)
    (suffix : raw = raw.take 688 ++ proof) (length : proof.length = 57607) :
    688 ≤ raw.length := by
  have sizes := congrArg List.length suffix
  simp only [List.length_append,List.length_take,length] at sizes
  omega

theorem drop_eq (raw proof : Bytes)
    (suffix : raw = raw.take 688 ++ proof) (length : proof.length = 57607) :
    raw.drop 688 = proof := by
  have size : (raw.take 688).length = 688 := by
    rw [List.length_take,Nat.min_eq_left (prefix_exists raw proof suffix length)]
  have same := congrArg (List.drop 688) suffix
  rw [List.drop_append,size,Nat.sub_self,List.drop_zero] at same
  have empty : (raw.take 688).drop 688 = [] := by
    simpa only [size] using (List.drop_length (l := raw.take 688))
  simpa only [empty,List.nil_append] using same

#print axioms prefix_exists
#print axioms drop_eq
end AspisR1.SCE_SuffixShape
end
