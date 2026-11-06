import NLF_FlagSemantics
import NLF_WrapperLaws
set_option autoImplicit false
namespace NLF_WrapperFlagLaws
open NLF_RefCell NLF_SdkModel NLF_FlagSemantics

def sharedAllowed (s : State) (i : Nat) : Prop := 0≤flag (s.cells i) ∧ flag (s.cells i)<9223372036854775807
instance (s : State) (i : Nat) : Decidable (sharedAllowed s i) := inferInstanceAs (Decidable (_ ∧ _))

theorem shared_complete (s : State) (i t : Nat) (fresh : t∉(s.cells i).readers) :
    wrap s i t .shared =
      if sharedAllowed s i then
        (put s i {s.cells i with readers:=t::(s.cells i).readers},.ok ⟨i,t,.shared⟩)
      else (s,.error .accountBorrowFailed) := by
  by_cases allowed : sharedAllowed s i
  · have hc := (shared_admission_iff (s.cells i)).mpr allowed
    rw [if_pos allowed]
    exact shared_result s i t hc.1 fresh hc.2
  · rw [if_neg allowed]
    apply wrapper_error
    have bad : ¬ ((s.cells i).writer=none ∧ (s.cells i).readers.length<9223372036854775807) :=
      fun h => allowed ((shared_admission_iff _).mp h)
    simp only [shared]
    split_ifs with h
    · exact False.elim (bad ⟨h.1,h.2.1⟩)
    · rfl

theorem exclusive_complete (s : State) (i t : Nat) :
    wrap s i t .exclusive =
      if flag (s.cells i)=0 then
        (put s i {s.cells i with writer:=some t},.ok ⟨i,t,.exclusive⟩)
      else (s,.error .accountBorrowFailed) := by
  by_cases allowed : flag (s.cells i)=0
  · have hc := (exclusive_admission_iff (s.cells i)).mpr allowed
    rw [if_pos allowed]
    exact exclusive_result s i t hc.1 hc.2
  · rw [if_neg allowed]
    apply wrapper_error
    have bad : ¬ ((s.cells i).writer=none ∧ (s.cells i).readers=[]) :=
      fun h => allowed ((exclusive_admission_iff _).mp h)
    simp [exclusive,bad]

theorem scalar_complete (s : State) (i t : Nat) (f : Payload → Nat)
    (fresh : t∉(s.cells i).readers) :
    scalar s i t f = if sharedAllowed s i then (s,.ok (f (s.cells i).payload))
      else (s,.error .accountBorrowFailed) := by
  by_cases allowed : sharedAllowed s i
  · have hc := (shared_admission_iff (s.cells i)).mpr allowed
    rw [if_pos allowed]
    exact scalar_result s i t f hc.1 fresh hc.2
  · rw [if_neg allowed]
    unfold scalar
    rw [shared_complete s i t fresh,if_neg allowed]

#print axioms shared_complete
#print axioms exclusive_complete
#print axioms scalar_complete
end NLF_WrapperFlagLaws
