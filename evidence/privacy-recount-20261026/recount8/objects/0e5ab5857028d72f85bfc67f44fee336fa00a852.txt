import R1Z.ProverRwQueryMembership
import Query31ExplicitScanConcreteSteps

/-! Source duplicate/fresh updates transported to the retained Q22 state. -/
set_option autoImplicit false
namespace R1Z.ProverRwQueryTransition
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryContains
open Query31ExplicitScanBody Query31ExplicitScanConcreteSteps

def advance (s : CurrentScan) (candidate : U32) : Result CurrentScan := do
  let seen ← host_transcript.query_contains s.accepted s.accepted_len candidate
  if seen then
    ok {s with draws := Usize.wrapping_add s.draws 1#usize}
  else
    let updated ← Array.update s.accepted s.accepted_len candidate
    ok ⟨updated,Usize.wrapping_add s.accepted_len 1#usize,Usize.wrapping_add s.draws 1#usize⟩

theorem mem_take_iff {α : Type} (xs : List α) (n : Nat) (x : α) :
    x ∈ xs.take n ↔ ∃ j, j<n ∧ xs[j]?=some x := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp hj
    have lt : j<n := lt_of_lt_of_le bound (List.length_take_le _ _)
    exact ⟨j,lt,by rwa [List.getElem?_take_of_lt lt] at hj⟩
  · rintro ⟨j,lt,hj⟩
    exact ⟨j,by rwa [List.getElem?_take_of_lt lt]⟩

theorem mem_val_iff (xs : List U32) (candidate : U32) :
    candidate.val ∈ xs.map UScalar.val ↔ candidate ∈ xs := by
  rw [List.mem_map]
  constructor
  · rintro ⟨x,hx,he⟩
    have : x=candidate := UScalar.eq_of_val_eq he
    exact this ▸ hx
  · intro h; exact ⟨candidate,h,rfl⟩

theorem contains_model (s : CurrentScan) (candidate : U32) (bound : s.accepted_len.val ≤ 22) :
    host_transcript.query_contains s.accepted s.accepted_len candidate =
      ok (decide (candidate.val ∈ acceptedPrefix s)) := by
  have iff := ProverRwQueryMembership.contains_prefix_iff s.accepted s.accepted_len candidate bound
  have mem : candidate.val ∈ acceptedPrefix s ↔
      ∃ j, j<s.accepted_len.val ∧ s.accepted.val[j]?=some candidate := by
    exact (mem_val_iff _ candidate).trans (mem_take_iff _ _ _)
  rw [contains_exact _ _ _ bound] at iff ⊢
  by_cases yes : candidate.val ∈ acceptedPrefix s
  · have h := iff.mpr (mem.mp yes)
    simpa only [yes,decide_true] using h
  · have h : ProverRwQueryContains.contains s.accepted s.accepted_len candidate = false := by
      cases hb : ProverRwQueryContains.contains s.accepted s.accepted_len candidate
      · rfl
      · exact False.elim (yes (mem.mpr (iff.mp (by rw [hb]))))
    simp only [h,yes,decide_false]

theorem wrapping_succ (index : Usize) (bound : index.val<64) :
    (Usize.wrapping_add index 1#usize).val=index.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  have one : (1#usize).val=1 := rfl
  rw [one,Nat.mod_eq_of_lt]
  have big := (64#usize).hSize
  change 64 < UScalar.size .Usize at big
  omega

theorem advance_q22 (s : CurrentScan) (candidate : U32)
    (hlen : s.accepted_len.val<22) (hdraw : s.draws.val<64) :
    ∃ next, advance s candidate=ok next ∧
      next.accepted_len.val ≤ 22 ∧ next.draws.val=s.draws.val+1 ∧
      AspisV8R19.Q22WordScan.scan (q22StateOf s) [candidate.val] = (q22StateOf next,false) := by
  have active := active_q22_of_bounded_source s hlen hdraw
  have hd := wrapping_succ s.draws hdraw
  by_cases member : candidate.val ∈ acceptedPrefix s
  · refine ⟨{s with draws := Usize.wrapping_add s.draws 1#usize},?_,by simpa using (Nat.le_of_lt hlen),hd,?_⟩
    · simp only [advance,contains_model s candidate (by omega),member,decide_true,bind_tc_ok,if_true]
    · rw [q22_duplicate_transition _ _ active.1 active.2 member]
      simp only [q22StateOf,acceptedPrefix,hd]
  · have hi : s.accepted_len.val < s.accepted.length := by
      simpa only [Array.length,s.accepted.property,show (22#usize).val=22 from rfl] using hlen
    obtain ⟨updated,hu,_⟩ := Aeneas.Std.WP.spec_imp_exists (Array.update_spec s.accepted s.accepted_len candidate hi)
    have hn := wrapping_succ s.accepted_len (by omega)
    let next : CurrentScan := ⟨updated,Usize.wrapping_add s.accepted_len 1#usize,Usize.wrapping_add s.draws 1#usize⟩
    refine ⟨next,?_,by dsimp [next]; omega,hd,?_⟩
    · simp only [advance,contains_model s candidate (by omega),member,decide_false,bind_tc_ok,Bool.false_eq_true,if_false,hu]
      rfl
    · rw [q22_fresh_transition _ _ active.1 active.2 member]
      have shape := Query31ExplicitScanBody.q22_state_fresh_update s candidate updated
        (Usize.wrapping_add s.accepted_len 1#usize) (Usize.wrapping_add s.draws 1#usize) hu hi hn hd
      rw [shape]
      rfl

#print axioms mem_take_iff
#print axioms mem_val_iff
#print axioms contains_model
#print axioms wrapping_succ
#print axioms advance_q22
end R1Z.ProverRwQueryTransition
