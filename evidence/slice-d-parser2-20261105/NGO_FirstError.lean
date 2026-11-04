import NGO_DecodeFrame
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_FirstError
open NGD_DecodeTrace AspisR1DecodeKFullV10
def Terminal {N : Usize} {r : Record} {off byteOffset : Usize}
    (d : Domain N r off byteOffset) (halt : Nat) (final : Final N) : Prop :=
  (final.2=none ∧ halt=N.val) ∨
    ∃ (index : Usize) (live : index.val<N.val) (error : r1_wire.Error),
      halt=index.val ∧ final.2=some (.Err error) ∧ answer d index live=.Err error

/-- The first error leaves the failing slot AND the full original suffix
unchanged. Successful termination reaches exactly N. Arbitrary prestates. -/
theorem suffix {N : Usize} {r : Record} {off byteOffset : Usize}
    (d : Domain N r off byteOffset) (iter : Range) (out : Array Q N) (final : Final N)
    (trace : Trace d iter out final) (finish : iter.end=N)
    (bounded : iter.start.val≤N.val) :
    ∃ halt, iter.start.val≤halt ∧ halt≤N.val ∧ Terminal d halt final ∧
      ∀ j (inside : j<N.val), halt≤j →
        final.1.val[j]'(by rw [final.1.property];exact inside) =
          out.val[j]'(by rw [out.property];exact inside) := by
  induction trace with
  | done iter out next =>
    refine ⟨N.val,bounded,le_refl _,Or.inl ⟨rfl,rfl⟩,?_⟩
    intro j inside beyond;omega
  | reject iter nextIter index out live next error reply =>
    obtain ⟨indexEq,advance,sameEnd,active⟩ := NGO_IteratorIndex.from_some iter nextIter index next
    refine ⟨index.val,by rw [indexEq],by omega,Or.inr ⟨index,live,error,rfl,rfl,reply⟩,?_⟩
    intro j inside beyond;rfl
  | write iter nextIter index out updated live next q reply store final rest ih =>
    obtain ⟨indexEq,advance,sameEnd,active⟩ := NGO_IteratorIndex.from_some iter nextIter index next
    obtain ⟨halt,startBound,endBound,terminal,frame⟩ := ih (sameEnd.trans finish) (by rw [←indexEq] at advance;omega)
    refine ⟨halt,by omega,endBound,terminal,?_⟩
    intro j inside beyond
    rw [frame j inside beyond]
    apply NGO_DecodeFrame.store_frame out updated index q live store j inside
    rw [←indexEq] at advance
    omega
#print axioms suffix
end NGO_FirstError
