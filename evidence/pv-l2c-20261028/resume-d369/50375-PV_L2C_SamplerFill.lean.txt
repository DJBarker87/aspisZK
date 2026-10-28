import PV_L2C_StateSampler
set_option autoImplicit false
namespace PV_L2C_SamplerFill
open Aeneas Aeneas.Std Result PV_L2C_StateSampler

def fill {S A : Type} (sample : Step S A) : Nat → Step S (List A)
  | 0 => pure []
  | n+1 => bind sample (fun a => bind (fill sample n) (fun rest => pure (a::rest)))

theorem returned {S A : Type} (sample : Step S A) (pred : A → Prop)
    (hs : ∀ s s1 a, sample s = ok (.ok a,s1) → pred a)
    (n : Nat) (s s1 : S) (values : List A)
    (h : fill sample n s = ok (.ok values,s1)) :
    values.length = n ∧ ∀ a ∈ values, pred a := by
  induction n generalizing s values with
  | zero => cases h;exact ⟨rfl,by simp⟩
  | succ n ih =>
    rw [fill] at h
    obtain ⟨a,after,ha,h⟩ := bind_returned _ _ _ _ _ h
    obtain ⟨rest,last,hr,h⟩ := bind_returned _ _ _ _ _ h
    cases h
    obtain ⟨hl,hc⟩ := ih after rest hr
    refine ⟨by simpa using hl,?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with he | ht
    · subst b;exact hs s after a ha
    · exact hc b ht
#print axioms returned

theorem scalar {S : Type} (next : S → Result (PV_L2C_M31.word × S))
    (n fuel : Nat) (s s1 : S) (values : List PV_L2C_M31.word)
    (h : fill (PV_L2C_StateSampler.scalar next fuel) n s = ok (.ok values,s1)) :
    values.length = n ∧ ∀ a ∈ values, PV_L2C_M31.canonical a :=
  returned _ _ (fun s s1 a ha => canonical_result next fuel s s1 a ha) n s s1 values h
#print axioms scalar

theorem secure {S : Type} (next : S → Result (PV_L2C_M31.word × S))
    (n fuel : Nat) (s s1 : S) (values : List PV_L2C_NativeQ.Q)
    (h : fill (PV_L2C_StateSampler.secure next fuel) n s = ok (.ok values,s1)) :
    values.length = n ∧ ∀ a ∈ values, PV_L2C_NativeQ.Canonical a :=
  returned _ _ (fun s s1 a ha => secure_result next fuel s s1 a ha) n s s1 values h
#print axioms secure
end PV_L2C_SamplerFill
