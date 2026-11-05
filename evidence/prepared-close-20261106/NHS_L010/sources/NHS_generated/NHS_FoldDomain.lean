import NHL_OpeningPacket
import JGi_FoldBuffers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_FoldDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Actual vector extensions determine S4's payload; no chosen payload length. -/
theorem produced (v : verifier.View) (root : Array U8 32#usize)
 (same : v.folded_root=some root) (tail : v.round1.val.length=224) :
 ∃ payload, NHL_PreparedOpening.foldPayload v=ok payload ∧
 payload.val=root.val++v.round1.val ∧ payload.val.length=256 := by
 obtain ⟨b1,b2,first,second,values⟩ := JGi_FoldBuffers.source root v.round1 tail
 refine ⟨alloc.vec.Vec.deref b2,?_,values,?_⟩
 · unfold NHL_PreparedOpening.foldPayload
   have add : (32#usize+224#usize : Result Usize)=ok 256#usize := rfl
   rw [add,bind_tc_ok,same]
   simp only [core.option.Option.unwrap,bind_tc_ok,lift]
   rw [first,bind_tc_ok,second,bind_tc_ok]
 · rw [values,List.length_append,tail]
   have size:=root.property
   change root.val.length=32 at size
   omega

/-- Every actual successful S4 payload is the produced256-byte value. -/
theorem bound (v : verifier.View) (root : Array U8 32#usize)
 (same : v.folded_root=some root) (tail : v.round1.val.length=224)
 (payload : Slice U8) (call : NHL_PreparedOpening.foldPayload v=ok payload) :
 payload.val.length≤2048 := by
 obtain ⟨out,run,_,size⟩ := produced v root same tail
 have equal := Result.ok.inj (run.symm.trans call)
 subst payload
 omega
#print axioms produced
#print axioms bound
end AspisR1.NHS_FoldDomain
