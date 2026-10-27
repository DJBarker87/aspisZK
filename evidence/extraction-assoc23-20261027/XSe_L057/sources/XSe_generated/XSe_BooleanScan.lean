import XSe_EnumeratedDriver
import CurrentCallerUsizeArithmeticV1
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_BooleanScan

def first {I : Type} (good : I → Bool) : List I → Nat → Option Nat
 | [],_ => none
 | item::rest,i => if good item then first good rest (i+1) else some i

def result {E : Type} (error : Usize → E) : Option Nat → Result (core.result.Result Unit E)
 | none => ok (.Ok ())
 | some i => if h : i≤UScalar.cMax .Usize then ok (.Err (error (UScalar.ofNat i h))) else fail .panic

def stage {I E : Type} (good : I → Bool) (error : Usize → E) (i : Usize) (item : I) :
 Result (core.result.Result Unit E) := ok (if good item then .Ok () else .Err (error i))
/-- The SAME first rejected item supplies the error index; the suffix is never
executed. The bound is solely the checked enumeration domain. -/
theorem source {I E : Type} (good : I → Bool) (error : Usize → E)
 (items : List I) (i : Usize) (bound : i.val+items.length≤UScalar.cMax .Usize) :
 XRo_Join_Carriers.mapR XSe_EnumeratedDriver.finish
  (XSe_ListDriver.fold (XSe_EnumeratedDriver.step (fun i => i+1#usize) (stage good error)) items (.Ok i))=
 result error (first good items i.val) := by
 induction items generalizing i with
 | nil => rfl
 | cons item rest ih =>
   let j : Usize := UScalar.ofNat (i.val+1) (by simp only [List.length_cons] at bound; omega)
   have hj : (i+1#usize : Result Usize)=ok j := by
    apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
   simp only [XSe_ListDriver.fold,XSe_EnumeratedDriver.step,stage,hj,bind_tc_ok]
   cases hg : good item with
   | false =>
     simp only [first,hg,Bool.false_eq_true,if_false,result,bind_tc_ok]
     rw [dif_pos (by scalar_tac)]
     cases rest <;> rfl
   | true =>
     simp only [first,hg,if_true,bind_tc_ok]
     exact ih j (by simp only [List.length_cons] at bound; change i.val+1+rest.length≤_;omega)
#print axioms source
end XSe_BooleanScan
