import R1Z.ProverRwSuccessBorrow
set_option autoImplicit false
namespace R1Z.ProverRwSuccessByteEquality
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

theorem list_compare (xs ys : List U8) (lengths : xs.length = ys.length) :
    List.allM (fun xy : U8 × U8 => Result.ok (decide (¬ core.cmp.impls.PartialEqU8.ne xy.1 xy.2)))
      (xs.zip ys) = Result.ok (decide (xs = ys)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all; rfl
  | cons a xs ih =>
    cases ys with
    | nil => simp_all
    | cons b ys =>
      have lens : xs.length=ys.length := by simpa using lengths
      by_cases h : a=b
      · subst b
        simpa [List.zip_cons_cons,List.allM,core.cmp.impls.PartialEqU8.ne] using ih ys lens
      · have hv : a.val ≠ b.val := by intro eq; apply h; exact UScalar.eq_of_val_eq eq
        simp [List.zip_cons_cons,List.allM,core.cmp.impls.PartialEqU8.ne,h,hv]
        rfl

theorem array_eq {N : Usize} (a b : Array U8 N) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b = .ok (decide (a=b)) := by
  unfold core.array.equality.PartialEqArray.eq
  have lengths : a.val.length=b.val.length := by rw [a.property,b.property]
  have lens : a.length=b.length := lengths
  simp only [lens,ite_true,liftFun2,lift,bind_tc_ok]
  rw [list_compare _ _ lengths]
  congr 2
  exact propext Subtype.val_inj
#print axioms list_compare
#print axioms array_eq
end R1Z.ProverRwSuccessByteEquality
