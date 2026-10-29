import R1Z.PV_RunJoin_ByteAppend38
import R1Z.PV_RunJoin_PublishContext57
set_option autoImplicit false
namespace R1Z.PV_RJN_Bytes
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_PublishSkeleton54

theorem length (xs : List U8) : (bytes xs).length=xs.length := List.length_map _

theorem append (xs ys : List U8) : bytes (xs++ys)=bytes xs++bytes ys := List.map_append

theorem append_success (out : alloc.vec.Vec U8) (s : Slice U8) (next : alloc.vec.Vec U8)
    (h : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s=ok next) :
    next.val=out.val++s.val := by
  by_cases room : out.length+s.length≤Usize.max
  · obtain ⟨v,hv,he⟩ := PV_RunJoin_ByteAppend38.append out s room
    have same := Result.ok.inj (hv.symm.trans h)
    subst next
    exact he
  · simp only [alloc.vec.Vec.extend_from_slice,dif_neg room] at h
    cases h

#print axioms length
#print axioms append
#print axioms append_success
end R1Z.PV_RJN_Bytes
