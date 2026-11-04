import NGO_IteratorIndex
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_DecodeFrame
open NGD_DecodeTrace AspisR1DecodeKFullV10
/-- Typed native assignment has exactly the library value/frame law. -/
theorem store_value {N : Usize} (out updated : Array Q N) (index : Usize) (q : Q)
    (live : index.val<N.val) (store : Array.update out index q=ok updated) :
    updated=out.set index q := by
  obtain ⟨v,run,value⟩ := WP.spec_imp_exists
    (Array.update_spec out index q (by simpa only [out.property] using live))
  rw [store] at run
  exact (Result.ok.inj run).trans value

theorem store_frame {N : Usize} (out updated : Array Q N) (index : Usize) (q : Q)
    (live : index.val<N.val) (store : Array.update out index q=ok updated)
    (j : Nat) (inside : j<N.val) (other : j≠index.val) :
    updated.val[j]'(by rw [updated.property];exact inside) =
      out.val[j]'(by rw [out.property];exact inside) := by
  rw [store_value out updated index q live store]
  simp only [Array.set_val_eq,List.getElem_set]
  simp [Ne.symm other]

/-- Every constructed trace preserves the already processed prefix on an
arbitrary prestate. It cannot invent a write at a previous native index. -/
theorem preserved_prefix {N : Usize} {r : Record} {off byteOffset : Usize}
    (d : Domain N r off byteOffset) (iter : Range) (out : Array Q N) (final : Final N)
    (trace : Trace d iter out final) :
    ∀ j (inside : j<N.val), j< iter.start.val →
      final.1.val[j]'(by rw [final.1.property];exact inside) =
        out.val[j]'(by rw [out.property];exact inside) := by
  induction trace with
  | done iter out next => intro j inside prior;rfl
  | reject iter nextIter index out live next error reply => intro j inside prior;rfl
  | write iter nextIter index out updated live next q reply store final rest ih =>
    obtain ⟨indexEq,advance,finish,active⟩ := NGO_IteratorIndex.from_some iter nextIter index next
    intro j inside prior
    rw [ih j inside (by omega)]
    apply store_frame out updated index q live store j inside
    subst index;omega
#print axioms store_value
#print axioms store_frame
#print axioms preserved_prefix
end NGO_DecodeFrame
