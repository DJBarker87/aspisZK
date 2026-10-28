import NDO_JFp_SHA256
set_option autoImplicit false
namespace AspisR1.JFp_SHA256

theorem blocks_chunks (cs : List (List Nat)) (lengths : ∀ b ∈ cs,b.length=64) :
    blocks cs.length cs.flatten=cs := by
  induction cs with
  | nil => rfl
  | cons b bs ih =>
    have hb := lengths b (List.mem_cons_self)
    have ht : ∀ c ∈ bs,c.length=64 := fun c hc => lengths c (List.mem_cons_of_mem b hc)
    simp only [List.length_cons,List.flatten_cons,blocks,List.take_append,List.drop_append,
      hb,List.take_of_length_le (by omega : b.length≤64),
      List.drop_eq_nil_of_le (by omega : b.length≤64),Nat.sub_self,List.take_zero,
      List.append_nil,List.nil_append]
    exact congrArg (List.cons b) (ih ht)

#print axioms blocks_chunks
end AspisR1.JFp_SHA256
