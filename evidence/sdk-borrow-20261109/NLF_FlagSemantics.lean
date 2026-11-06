import NLF_CounterLaws
set_option autoImplicit false
namespace NLF_FlagSemantics
open NLF_RefCell

theorem shared_admission_iff {α : Type} (c : Cell α) :
    (c.writer=none ∧ c.readers.length<9223372036854775807) ↔
    (0≤flag c ∧ flag c<9223372036854775807) := by
  cases hw : c.writer with
  | none => simp only [flag,hw,true_and,Int.ofNat_eq_natCast]; omega
  | some t => simp [flag,hw]

theorem exclusive_admission_iff {α : Type} (c : Cell α) :
    (c.writer=none ∧ c.readers=[]) ↔ flag c=0 := by
  cases hw : c.writer with
  | none => simp [flag,hw]
  | some t => simp [flag,hw]

theorem shared_max_error {α : Type} (c : Cell α) (t : Nat)
    (max : flag c=9223372036854775807) : shared c t = .error .conflict := by
  have bad : ¬ (c.writer=none ∧ c.readers.length<9223372036854775807) := by
    intro h
    have := shared_admission_iff c |>.mp h
    omega
  simp only [shared]
  split_ifs with h
  · exact False.elim (bad ⟨h.1,h.2.1⟩)
  · rfl

#print axioms shared_admission_iff
#print axioms exclusive_admission_iff
#print axioms shared_max_error
end NLF_FlagSemantics
