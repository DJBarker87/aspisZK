import NHL_Packets
set_option autoImplicit false
namespace AspisR1.NHL_SplitPacket
open Aeneas Aeneas.Std Result

theorem sizes (logical : alloc.vec.Vec U8)
 (parts : (Slice U8×Slice U8) × ((Slice U8×Slice U8)→Slice U8))
 (size : logical.val.length=14759)
 (run : core.slice.Slice.split_at_mut (alloc.vec.Vec.deref_mut logical).1 13831#usize=ok parts) :
 parts.1.1.val.length=13831 ∧ parts.1.2.val.length=928 := by
 have bound : 13831#usize≤(alloc.vec.Vec.deref_mut logical).1.length := by
   change 13831≤logical.val.length
   omega
 obtain ⟨derived,call,facts⟩ := WP.spec_imp_exists
   (core.slice.Slice.split_at_mut.spec (alloc.vec.Vec.deref_mut logical).1 13831#usize bound)
 have same : derived=parts := Result.ok.inj (call.symm.trans run)
 subst derived
 refine ⟨facts.1,?_⟩
 have rest:=facts.2.1
 change parts.1.2.val.length=logical.val.length-13831 at rest
 omega
#print axioms sizes
end AspisR1.NHL_SplitPacket
