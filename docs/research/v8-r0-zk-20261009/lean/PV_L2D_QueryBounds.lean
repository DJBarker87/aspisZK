import PV_L2D_QueryScan
set_option autoImplicit false
namespace PV_L2D_QueryBounds
open PV_L2D_QueryScan

def Admitted (s : State) : Prop :=
  s.accepted.Nodup ∧ (∀ x∈s.accepted,x<2^18) ∧
  s.accepted.length≤22 ∧ s.draws≤64 ∧ s.accepted.length≤s.draws

theorem initial : Admitted ⟨[],0⟩ := by simp [Admitted]
#print axioms initial

theorem next_admitted (s : State) (x : Nat) (h : Admitted s)
    (not_stopped : stopped s=false) (small : x<2^18) : Admitted (next s x) := by
  rcases h with ⟨hn,hb,hl,hd,hld⟩
  have ns : s.accepted.length≠22 ∧ s.draws≠64 := by simpa [stopped] using not_stopped
  by_cases hx : x∈s.accepted
  · simpa [Admitted,next,hx] using And.intro hn (And.intro hb (by omega))
  · simp only [Admitted,next,hx,ite_false,List.length_append,List.length_singleton]
    refine ⟨?_,?_,by omega,by omega,by omega⟩
    · simpa using hn.append (by simp) (by simpa using hx)
    · intro y hy
      simp only [List.mem_append,List.mem_singleton] at hy
      rcases hy with hy|rfl
      · exact hb y hy
      · exact small
#print axioms next_admitted

theorem scan_admitted (s : State) (xs : List Nat) (h : Admitted s)
    (small : ∀ x∈xs,x<2^18) : Admitted (scan s xs).2 := by
  induction xs generalizing s with
  | nil => exact h
  | cons x xs ih =>
    by_cases hs : stopped s=true
    · simpa [scan,hs] using h
    · have hf : stopped s=false := by cases h' : stopped s <;> simp_all
      simp only [scan,hf,Bool.false_eq_true,ite_false]
      exact ih (next s x) (next_admitted s x h hf (small x (by simp)))
        (fun y hy=>small y (by simp [hy]))
#print axioms scan_admitted

theorem member_read_safe (s : State) (h : Admitted s) (i : Nat) (hi : i<s.accepted.length) :
    i<22 := lt_of_lt_of_le hi h.2.2.1
#print axioms member_read_safe

theorem write_safe (s : State) (h : Admitted s) (hs : stopped s=false) :
    s.accepted.length<22 := by
  have : s.accepted.length≠22 := by
    intro he
    simp [stopped,he] at hs
  have:=h.2.2.1
  omega
#print axioms write_safe

theorem masked_bound (w : UInt32) : w.toNat % 262144<2^18 := by
  exact Nat.mod_lt _ (by decide)
#print axioms masked_bound
end PV_L2D_QueryBounds
