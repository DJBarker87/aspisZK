import LIB_Env
set_option autoImplicit false
noncomputable section
namespace LIBC_HashPartitions
open RSL
/-- The two native hash address families are disjoint by total length:
node 1+32+32; private leaf 2+(128 or480)+32. -/
def split (b : Bytes) : List Bytes :=
 let n := if b.length=65 then 1 else 2
 [b.take n,(b.drop n).take (b.length-n-32),b.drop (b.length-32)]
def Shape (parts : List Bytes) : Prop := ∃ h v s,
 parts=[h,v,s] ∧ s.length=32 ∧
 ((h.length=1 ∧ v.length=32) ∨ (h.length=2 ∧ (v.length=128 ∨ v.length=480)))
theorem split_append (h v s : Bytes) (hs : s.length=32)
 (width : (h.length=1 ∧ v.length=32) ∨ (h.length=2 ∧ (v.length=128 ∨ v.length=480))) :
 split (h++v++s)=[h,v,s] := by
 have total : (h++v++s).length=h.length+v.length+32 := by simp only [List.length_append,hs]
 have header : (if (h++v++s).length=65 then 1 else 2)=h.length := by
  rcases width with ⟨hh,hv⟩ | ⟨hh,hv | hv⟩ <;> simp [hh,hv,hs]
 have body : (h++v++s).length-h.length-32=v.length := by omega
 have tail : (h++v++s).length-32=h.length+v.length := by omega
 unfold split
 rw [header]
 dsimp only
 rw [body,tail]
 simp only [List.append_assoc,List.take_left,List.drop_left,List.take_append,List.take_length,
  Nat.sub_self,List.take_zero,List.append_nil,List.drop_append,List.drop_length,List.nil_append]
 simp
theorem exact (parts : List Bytes) (shape : Shape parts) : split parts.flatten=parts := by
 obtain ⟨h,v,s,rfl,hs,hv⟩ := shape
 simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using split_append h v s hs hv
#print axioms split_append
#print axioms exact
end LIBC_HashPartitions
