import R1Z.ProverRw18FieldPowerPure
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FoldAppend
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

theorem run (step : U32 → (Q × Q) → Result (Q × Q))
    (left right : List U32) (state : Q × Q) :
    PV_RW_CompressStep.run step (left++right) state=(do
      let middle ← PV_RW_CompressStep.run step left state
      PV_RW_CompressStep.run step right middle) := by
  induction left generalizing state with
  | nil => rfl
  | cons value values ih => simp only [List.cons_append,PV_RW_CompressStep.run,ih,bind_assoc_eq]

theorem owned (left right : List U32) (lambda : Q) (state : Q × Q) :
    PV_RW_CompressClosedFold.owned (left++right) lambda state=(do
      let middle ← PV_RW_CompressClosedFold.owned left lambda state
      PV_RW_CompressClosedFold.owned right lambda middle) :=
  run _ left right state

theorem fail_prefix (left right : List U32) (lambda : Q) (state : Q × Q) (error : Error)
    (failed : PV_RW_CompressClosedFold.owned left lambda state=fail error) :
    PV_RW_CompressClosedFold.owned (left++right) lambda state=fail error := by
  rw [owned,failed];rfl

theorem div_prefix (left right : List U32) (lambda : Q) (state : Q × Q)
    (diverged : PV_RW_CompressClosedFold.owned left lambda state=div) :
    PV_RW_CompressClosedFold.owned (left++right) lambda state=div := by
  rw [owned,diverged];rfl

#print axioms run
#print axioms owned
#print axioms fail_prefix
#print axioms div_prefix
end R1Z.ProverRw18FoldAppend
