import NDD_PackSealed
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_PackComposition
open FIq_Native NDD_PackModel NDD_PackSealed

def paddingCut (values : Slice field.QM31) :
    Result (field.QM31 × field.QM31 × field.QM31 × field.QM31) :=
  concrete.run values (fun a b c d => ok (a,b,c,d))

/-- Composition over the checked concrete prefix (linked separately to the
actual cohort body by NDD_PackSealed.concrete_source); native copy and arithmetic
span association remain separate P6 obligations. -/
theorem source_reference (values : Slice field.QM31) :
    (do let q ← concrete.run values tail;ok (words q)) = (do
      let (v0,v1,v2,v3) ← paddingCut values
      NDD_Reference.pack_ref
        (Array.make 4#usize [words v0,words v1,words v2,words v3])) := by
  let encode : field.QM31 → Result (Array U32 4#usize) := fun q => ok (words q)
  let ref4 : field.QM31 → field.QM31 → field.QM31 → field.QM31 → Result (Array U32 4#usize) :=
    fun a b c d => NDD_Reference.pack_ref (Array.make 4#usize [words a,words b,words c,words d])
  let tupleRef : field.QM31 × field.QM31 × field.QM31 × field.QM31 → Result (Array U32 4#usize) :=
    fun (a,b,c,d) => ref4 a b c d
  have arithmetic : (fun a b c d => do let q ← tail a b c d; encode q) = ref4 := by
    funext a b c d
    exact (reference_tail a b c d).symm
  have beta : (fun a b c d => do let t ← ok (a,b,c,d); tupleRef t) = ref4 := by
    funext a b c d
    rfl
  have h2 := concrete.bind values tail encode
  have h3 := congrArg (concrete.run values) arithmetic
  have h4 := concrete.bind values (fun a b c d => ok (a,b,c,d)) tupleRef
  have h5 := congrArg (concrete.run values) beta
  exact h2.trans (h3.trans (h4.trans h5).symm)
#print axioms source_reference
end NDD_PackComposition
