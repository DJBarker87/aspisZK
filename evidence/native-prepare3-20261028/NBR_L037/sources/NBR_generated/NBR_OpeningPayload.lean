import NBR_OpeningConstruct
import KMX_CopyMeaning
set_option autoImplicit false
namespace AspisR1.NBR_OpeningPayload
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem source {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (trace : NBL_OpeningTrace.Trace D sem view hash) (roundSize : view.round1.val.length=224) :
    trace.bytes1.val=trace.root.val ∧
    trace.bytes2.val=trace.root.val++view.round1.val ∧
    trace.bytes2.val.length=256 := by
  have first := NBR_VecAppend.extend (alloc.vec.Vec.with_capacity U8 256#usize)
    (Array.to_slice trace.root) (by
      change 0+trace.root.val.length≤Usize.max
      rw [trace.root.property]
      scalar_tac)
  have same1 := congrArg (fun v : alloc.vec.Vec U8 => v.val)
    (Result.ok.inj (first.symm.trans trace.appendRoot))
  have pure1 : (alloc.vec.Vec.with_capacity U8 256#usize).val++trace.root.val=trace.bytes1.val := same1
  have empty : (alloc.vec.Vec.with_capacity U8 256#usize).val=([] : List U8) := rfl
  have bytes1 : trace.bytes1.val=trace.root.val := by
    simpa only [empty,List.nil_append] using pure1.symm
  have firstSize : trace.bytes1.val.length=32 := by rw [bytes1];exact trace.root.property
  have second := NBR_VecAppend.extend trace.bytes1 view.round1 (by
    change trace.bytes1.val.length+view.round1.val.length≤Usize.max
    rw [firstSize,roundSize]
    scalar_tac)
  have same2 := congrArg (fun v : alloc.vec.Vec U8 => v.val)
    (Result.ok.inj (second.symm.trans trace.appendRound))
  have pure2 : trace.bytes1.val++view.round1.val=trace.bytes2.val := same2
  have bytes2 : trace.bytes2.val=trace.root.val++view.round1.val :=
    pure2.symm.trans (congrArg (fun xs : List U8 => xs++view.round1.val) bytes1)
  exact ⟨bytes1,bytes2,by rw [bytes2,List.length_append,trace.root.property,roundSize];rfl⟩

/-- Capacity invariant for ONE native push at every reached append position.
The two loops' dimensions are proved from the actual caller view. -/
theorem push_bound (roundSize : Nat) (size : roundSize=224) (i : Nat) :
    (i<32 → i<256) ∧ (i<roundSize → 32+i<256) := by omega

#print axioms source
#print axioms push_bound
end AspisR1.NBR_OpeningPayload
