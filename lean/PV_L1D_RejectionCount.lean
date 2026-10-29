import PV_L1D_CountSuccess
set_option autoImplicit false
namespace PV_L1D_RejectionCount
open R1Z.SideChannelL1AttemptRecord
open R1Z.ProverCommitRetry34 (Published)
variable {S P : Type}
def retrying (a : Attempt P) : Bool :=
  match a.result with | .retry => true | _ => false
/-- Rejected body attempts precede the successful attempt, so successful
entered/rejected counts are jointly determined by the original run. -/
theorem success_rejections (owner : Owner S P) (fuel index : Nat) (s : S)
    (p : Published P) (h : (run owner fuel index s).1.result = .done p) :
    ((run owner fuel index s).1.attempts.filter retrying).length + 1 =
      (run owner fuel index s).1.attempts.length := by
  induction fuel generalizing index s with
  | zero => cases h
  | succ fuel ih =>
    cases step : owner index s with
    | mk record after =>
      cases hr : record.result with
      | done proof =>
        simp only [run,step,hr,retrying,List.filter_cons,List.filter_nil,List.length_cons,List.length_nil]
        simp only [hr,Bool.false_eq_true,if_false,List.length_nil]
      | stop e => simp only [run,step,hr] at h; cases h
      | retry =>
        simp only [run,step,hr] at h ⊢
        have rest := ih (index+1) after h
        simp only [List.filter_cons,retrying,hr,if_true,List.length_cons]
        omega
#print axioms success_rejections

theorem original_count_pair (owner : Owner S P) (s : S) (p : Published P)
    (h : (run owner 8 0 s).1.result = .done p) :
    ((run owner 8 0 s).1.attempts.length,
      ((run owner 8 0 s).1.attempts.filter retrying).length) =
        (p.attempts,p.attempts-1) := by
  have hc := PV_L1D_CountSuccess.count_eq_entered owner 8 0 s p h
  have hr := success_rejections owner 8 0 s p h
  apply Prod.ext <;> simp only [Prod.fst,Prod.snd] <;> omega
#print axioms original_count_pair
end PV_L1D_RejectionCount
