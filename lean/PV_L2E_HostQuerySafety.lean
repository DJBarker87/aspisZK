import PV_L2E_HostQueryValue
set_option autoImplicit false
namespace PV_L2E_HostQuerySafety
open PV_L2D_QueryScan PV_L2D_QueryBounds PV_L2E_HostQuery

def Safe : PV_L2E_HostQuery.Event → Prop
  | .readByte b o => b<8 ∧ o<32
  | .compare i _ => i<22
  | .writeQuery i => i<22
  | .selectAdvance i => i<8
  | _ => True

theorem member_safe (x i : Nat) (xs : List Nat) (cap : i+xs.length≤22) :
    ∀ e∈(member x i xs).2.flatMap comparisons, Safe e := by
  induction xs generalizing i with
  | nil => simp [member]
  | cons y ys ih =>
    by_cases h : x=y
    · simp [member,h,comparisons,Safe]
      simp only [List.length_cons] at cap
      omega
    · have ht := ih (i+1) (by simpa only [List.length_cons] using cap)
      simp only [member,if_neg h,List.flatMap_cons,comparisons,List.singleton_append,
        List.mem_cons]
      intro e he
      rcases he with rfl|he
      · dsimp [Safe]; simp only [List.length_cons] at cap; omega
      · exact ht e he

/-- All guards and accesses emitted by the complete recursive host model
are safe, including failure prefixes and final-word success. No accepted-only
restriction or assumption that duplicate scans complete early is needed. -/
theorem run_safe (s : State) (words : List Nat) (admitted : Admitted s)
    (small : ∀ x∈words,x<2^18) :
    ∀ e∈(PV_L2E_HostQuery.run s words).2, Safe e := by
  induction words generalizing s with
  | nil =>
    rw [PV_L2E_HostQuery.run.eq_def]
    split_ifs <;> simp_all [Safe]
    have hd := admitted.2.2.2.1
    omega
  | cons x xs ih =>
    by_cases hd : s.draws=64
    · rw [at_cap s (x::xs) hd]
      split_ifs <;> simp [Safe]
    · by_cases ha : s.accepted.length=22
      · rw [PV_L2E_HostQuery.complete s (x::xs) hd ha]
        simp only [List.mem_cons,List.not_mem_nil,or_false]
        intro e he
        rcases he with rfl|rfl|rfl
        · trivial
        · trivial
        · dsimp [Safe]; have hb := admitted.2.2.2.1; omega
      · have live : stopped s=false := by simp [stopped,ha,hd]
        have hb := read_safe s admitted live
        have hw := write_safe s admitted live
        have hm := member_safe x 0 s.accepted (by simpa using admitted.2.2.1)
        have ht := ih (next s x)
          (next_admitted s x admitted live (small x (by simp)))
          (fun y hy => small y (by simp [hy]))
        rw [PV_L2E_HostQuery.run.eq_def,if_neg hd,if_neg ha]
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
        intro e he
        rcases he with (rfl|rfl)|(rfl|rfl|rfl|rfl)|he|he|he
        · trivial
        · trivial
        · exact ⟨hb.1,hb.2 0 (by decide)⟩
        · exact ⟨hb.1,hb.2 1 (by decide)⟩
        · exact ⟨hb.1,hb.2 2 (by decide)⟩
        · exact ⟨hb.1,hb.2 3 (by decide)⟩
        · exact hm e he
        · split_ifs at he <;> simp_all [Safe]
        · exact ht e he

#print axioms member_safe
#print axioms run_safe
end PV_L2E_HostQuerySafety
