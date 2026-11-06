import NLF_ViewLaws
import NLF_ReleaseInvariant
set_option autoImplicit false
namespace NLF_StateLaws
open NLF_RefCell NLF_SdkModel NLF_ParentModel

theorem put_put (s : State) (i : Nat) (c d : Cell Payload) :
    put (put s i c) i d = put s i d := by
  cases s; simp only [put]; congr; funext j; split_ifs <;> simp_all

theorem put_commute (s : State) (i j : Nat) (c d : Cell Payload) (hne : i≠j) :
    put (put s i c) j d = put (put s j d) i c := by
  cases s; simp only [put]; congr; funext k; split_ifs <;> simp_all

theorem write_valid (s : State) (g : Guard) (v : Payload) (h : ValidState s) :
    ValidState (NLF_ViewLaws.write s g v) := by
  apply put_valid _ _ _ h
  exact h g.cell

theorem write_invariant (p : Parent) (g : Guard) (v : Payload) (h : Invariant p) :
    Invariant {p with state := NLF_ViewLaws.write p.state g v} := by
  apply subset_invariant p.state _ p.next h (write_valid _ _ _ h.1)
  intro i t ht
  by_cases eq : i=g.cell <;> simpa [NLF_ViewLaws.write,put,eq,HasToken] using ht

theorem write_release (s : State) (i t : Nat) (v : Payload)
    (free : (s.cells i).writer=none) :
    NLF_SdkModel.release (NLF_ViewLaws.write (put s i {s.cells i with writer:=some t}) ⟨i,t,.exclusive⟩ v)
      ⟨i,t,.exclusive⟩ = .ok (put s i {s.cells i with payload:=v}) := by
  simp only [NLF_ViewLaws.write,put_same,put_put,NLF_SdkModel.release]
  simp only [dropExclusive,↓reduceIte]
  simp [free]

#print axioms put_put
#print axioms put_commute
#print axioms write_valid
#print axioms write_invariant
#print axioms write_release
end NLF_StateLaws
