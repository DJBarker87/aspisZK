import R1Z.BuilderRecordsArray
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ArrayShapes16
open Aeneas Aeneas.Std

theorem shape3 {α : Type} [Inhabited α] (a : Array α 3#usize) :
    a = Array.make 3#usize [a.val[0]!, a.val[1]!, a.val[2]!] := by
  apply BuilderRecordCanonical.array_ext
  intro i hi
  have bound : i < 3 := by simpa using hi
  interval_cases i <;> rfl

#print axioms shape3

theorem shape20 {α : Type} [Inhabited α] (a : Array α 20#usize) :
    a = Array.make 20#usize [a.val[0]!, a.val[1]!, a.val[2]!, a.val[3]!, a.val[4]!, a.val[5]!, a.val[6]!, a.val[7]!, a.val[8]!, a.val[9]!, a.val[10]!, a.val[11]!, a.val[12]!, a.val[13]!, a.val[14]!, a.val[15]!, a.val[16]!, a.val[17]!, a.val[18]!, a.val[19]!] := by
  apply BuilderRecordCanonical.array_ext
  intro i hi
  have bound : i < 20 := by simpa using hi
  interval_cases i <;> rfl

#print axioms shape20

theorem shape21 {α : Type} [Inhabited α] (a : Array α 21#usize) :
    a = Array.make 21#usize [a.val[0]!, a.val[1]!, a.val[2]!, a.val[3]!, a.val[4]!, a.val[5]!, a.val[6]!, a.val[7]!, a.val[8]!, a.val[9]!, a.val[10]!, a.val[11]!, a.val[12]!, a.val[13]!, a.val[14]!, a.val[15]!, a.val[16]!, a.val[17]!, a.val[18]!, a.val[19]!, a.val[20]!] := by
  apply BuilderRecordCanonical.array_ext
  intro i hi
  have bound : i < 21 := by simpa using hi
  interval_cases i <;> rfl

#print axioms shape21
end R1Z.PV_RunJoin_ArrayShapes16
