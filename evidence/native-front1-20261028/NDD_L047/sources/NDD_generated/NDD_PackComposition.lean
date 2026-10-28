import NDD_PackPrefix
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_PackComposition
open FIq_Native NDD_PackModel NDD_PackPrefix

def paddingCut (values : Slice field.QM31) :
    Result (field.QM31 × field.QM31 × field.QM31 × field.QM31) :=
  prefixWith values (fun a b c d => ok (a,b,c,d))

/-- Same-execution composition on the cohort side; native copy and arithmetic
span association remain separate P6 obligations. -/
theorem source_reference (values : Slice field.QM31) :
    (do let q ← field.qm31_pack_base4 values;ok (words q)) = (do
      let (v0,v1,v2,v3) ← paddingCut values
      NDD_Reference.pack_ref
        (Array.make 4#usize [words v0,words v1,words v2,words v3])) := by
  rw [source_prefix]
  unfold paddingCut
  rw [bind_prefix,bind_prefix]
  simp only [bind_tc_ok]
  apply congrArg (prefixWith values)
  funext a b c d
  exact (reference_tail a b c d).symm
#print axioms source_reference
end NDD_PackComposition
