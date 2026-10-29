import NEA_Reference.Funs
import R17CurrentM31Semantics
import ExtractedCurrentM31AddSub
import NDD_ScalarCanon
set_option autoImplicit false
namespace NEA_LineTail
open Aeneas Aeneas.Std Result
abbrev M := AspisR1Qm31ArithmeticProbe.field.M31

theorem sub_one (d : U32) (canonical : d.val < 2147483647) :
    (if d >= 1#u32 then (UScalar.sub d 1#u32 : Result U32) else UScalar.sub 2147483647#u32 1#u32) =
      AspisR1Qm31ArithmeticProbe.field.M31.sub d 1#u32 := by
  obtain ⟨out,run,value,_⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod
    d 1#u32 canonical (by decide)
  rw [run]
  split
  · have positive : (1#u32).val ≤ d.val := by scalar_tac
    change 1 ≤ d.val at positive
    obtain ⟨z,raw,zvalue⟩ := AspisR1.ExtractedMaskReducerOps.sub_success d 1#u32 positive
    have equal : z=out := by
      apply UScalar.eq_of_val_eq
      rw [zvalue,value]
      change d.val-1=(d.val+2147483647-1)%2147483647
      omega
    simpa only [equal] using raw
  · have zero : d=0#u32 := UScalar.eq_of_val_eq (by scalar_tac)
    subst d
    have expected : out.val=2147483646 := by
      rw [value]
      rfl
    obtain ⟨z,raw,zvalue⟩ := AspisR1.ExtractedMaskReducerOps.sub_success
      2147483647#u32 1#u32 (by decide)
    have equal : z=out := UScalar.eq_of_val_eq (by rw [zvalue,expected];rfl)
    simpa only [equal] using raw

theorem reference (s : U32) (canonical : s.val < 2147483647) :
    NEA_Reference.line_double_sub_ref s = (do
      let d ← AspisR1Qm31ArithmeticProbe.field.M31.double s
      AspisR1Qm31ArithmeticProbe.field.M31.sub d 1#u32) := by
  obtain ⟨d,run,_,cd⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod s s canonical canonical
  have doubled : AspisR1Qm31ArithmeticProbe.field.M31.double s=ok d := by
    simpa only [AspisR1Qm31ArithmeticProbe.field.M31.double] using run
  calc
    NEA_Reference.line_double_sub_ref s =
        (do let d ← AspisR1Qm31ArithmeticProbe.field.M31.double s
            if d >= 1#u32 then UScalar.sub d 1#u32 else UScalar.sub 2147483647#u32 1#u32) := by
      simp only [NEA_Reference.line_double_sub_ref,
        AspisR1Qm31ArithmeticProbe.field.M31.double,
        AspisR1Qm31ArithmeticProbe.field.M31.add,
        AspisR1Qm31ArithmeticProbe.field.P,bind_assoc_eq,NDD_ResultLaws.bind_return,HSub.hSub,Aeneas.Std.instHSubUScalarResult]
    _ = _ := by
      rw [doubled]
      simpa only [bind_tc_ok] using sub_one d cd

#print axioms sub_one
#print axioms reference
end NEA_LineTail
