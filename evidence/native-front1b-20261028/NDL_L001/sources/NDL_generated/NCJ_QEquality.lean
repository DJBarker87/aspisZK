import FIo_NativeFuns
set_option autoImplicit false
noncomputable section
namespace NCJ_QEquality
open Aeneas Aeneas.Std Result FIo_Native
attribute [local instance] Classical.propDecidable
abbrev Q := aspis_core.field.QM31

theorem cm (x y : aspis_core.field.CM31) :
    aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq x y = ok (decide (x=y)) := by
  cases x
  cases y
  simp [aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]
  split <;> simp_all

theorem qm (x y : Q) :
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq x y = ok (decide (x=y)) := by
  cases x
  cases y
  simp [aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,cm]
  split <;> simp_all

theorem lists (xs ys : List Q) (hlen : xs.length = ys.length) :
    List.allM (fun (x,y) => do
      let b ← aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.ne x y
      ok (decide (¬ b = true))) (xs.zip ys) = ok (decide (xs=ys)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [List.allM,pure]
  | cons x xs ih =>
    cases ys with
    | nil => simp_all
    | cons y ys =>
      have tail : xs.length=ys.length := by simpa using hlen
      rw [List.zip_cons_cons]
      simp only [List.allM]
      have eqv : (do let b ← aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.ne x y; ok (decide (¬ b = true))) = ok (decide (x=y)) := by
        simp [aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31,
          core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,qm]
      rw [eqv]
      by_cases same : x=y
      · simp only [same,decide_true,bind_tc_ok,if_pos]
        simpa only [List.cons.injEq,true_and,liftFun2,bind_tc_ok] using ih ys tail
      · simp [same,pure]

theorem arrays {n : Usize} (a b : Array Q n) :
    core.array.equality.PartialEqArray.eq aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 a b =
      ok (decide (a=b)) := by
  unfold core.array.equality.PartialEqArray.eq
  have len : a.length=b.length := by have:=a.property;have:=b.property;scalar_tac
  rw [if_pos len,lists a.val b.val (by have:=a.property;have:=b.property;scalar_tac)]
  have eqv : (a.val=b.val) ↔ a=b := ⟨Subtype.ext,fun h => congrArg Subtype.val h⟩
  simp only [eqv]

#print axioms cm
#print axioms qm
#print axioms lists
#print axioms arrays
end NCJ_QEquality
