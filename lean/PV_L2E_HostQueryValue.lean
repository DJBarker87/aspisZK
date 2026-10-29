import PV_L2E_HostQuery
set_option autoImplicit false
namespace PV_L2E_HostQueryValue
open PV_L2D_QueryScan PV_L2E_HostQuery

def finish (s : State) : PV_L2E_HostQuery.Result :=
  if s.accepted.length=22 then .ok s.accepted (if s.draws=64 then 7 else s.draws/8)
  else .exhausted

/-- Complete recursive host result equals the existing mathematical scanner,
including the final draw-64 success/error split. Domain includes failures. -/
theorem complete_result (s : State) (words : List Nat)
    (remaining : s.draws+words.length=64) :
    (PV_L2E_HostQuery.run s words).1=finish (scan s words).2 := by
  induction words generalizing s with
  | nil =>
    have hd : s.draws=64 := by simpa using remaining
    rw [at_cap s [] hd]
    by_cases ha : s.accepted.length=22 <;> simp [ha,finish,scan,hd]
  | cons x xs ih =>
    by_cases hd : s.draws=64
    · rw [at_cap s (x::xs) hd]
      by_cases ha : s.accepted.length=22 <;> simp [ha,finish,scan,stopped,hd]
    · by_cases ha : s.accepted.length=22
      · rw [PV_L2E_HostQuery.complete s (x::xs) hd ha]
        simp [scan,stopped,ha,finish,hd]
      · have hn : stopped s=false := by simp [stopped,ha,hd]
        have ht : (next s x).draws+xs.length=64 := by
          simp only [next,List.length_cons] at remaining ⊢
          omega
        rw [PV_L2E_HostQuery.run.eq_def,if_neg hd,if_neg ha]
        simpa only [scan,hn,Bool.false_eq_true,↓reduceIte] using ih (next s x) ht

theorem no_missing_word (s : State) (words : List Nat)
    (remaining : s.draws+words.length=64) :
    (PV_L2E_HostQuery.run s words).1≠.missingWord := by
  rw [complete_result s words remaining]
  unfold finish
  split <;> simp

#print axioms complete_result
#print axioms no_missing_word
end PV_L2E_HostQueryValue
