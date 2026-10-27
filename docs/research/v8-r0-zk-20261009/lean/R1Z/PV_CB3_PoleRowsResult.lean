import R1Z.PV_CB3_ResultScan
import R1Z.PV_CB3_PoleBoolean
set_option autoImplicit false
namespace R1Z.PV_CB3_PoleRowsResult
open Aeneas Aeneas.Std Result

def rowTest (active a b c d : Bool) : Result Bool :=
  ok (!(active && (a || b || c || d)))

theorem row_step (clear active a b c d : Bool) :
    (do let b ← rowTest active a b c d; ok (clear && b)) =
      ok (PV_CB3_PoleBoolean.row clear active a b c d) := by
  simp only [rowTest,bind_tc_ok,PV_CB3_PoleBoolean.row_value]

theorem pure_scan {α : Type} (test : α → Bool) (clear : Bool) (xs : List α) :
    PV_CB3_ResultScan.scan (fun x => ok (test x)) clear xs = ok (clear && xs.all test) := by
  induction xs generalizing clear with
  | nil => simp only [PV_CB3_ResultScan.nil,List.all_nil,Bool.and_true]
  | cons x xs ih =>
    simp only [PV_CB3_ResultScan.cons,bind_tc_ok,ih,List.all_cons,Bool.and_assoc]
#print axioms row_step
#print axioms pure_scan
end R1Z.PV_CB3_PoleRowsResult
