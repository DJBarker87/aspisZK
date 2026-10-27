import XRm_WideProducer
import XRk_PowersAssociation
import XRk_ScratchProjection
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal XRk_ResultTools XRm_WideProducer
namespace XRm_PowersCanonical
/-- Symbolic induction over the reference recurrence already identified with
the SAME actual emitted powers loop. Gamma needs no canonicality premise. -/
theorem recurrence (gamma : XRk_Wide) (n : Nat) (p : XRk_Wide)
    (xs : List XRk_Wide) (hp : Canonical p)
    (run : XRk_powers gamma n p=ok xs) : ∀ e ∈ xs, Canonical e := by
  induction n generalizing p xs with
  | zero =>
    have same := Result.ok.inj run
    subst xs
    intro e member
    cases member
  | succ n ih =>
    cases n with
    | zero =>
      have same := Result.ok.inj run
      subst xs
      intro e member
      have he := List.mem_singleton.mp member
      subst e
      exact hp
    | succ n =>
      unfold XRk_powers at run
      obtain ⟨next,hnext,run⟩ := bind_success _ _ _ run
      obtain ⟨rest,hrest,run⟩ := bind_success _ _ _ run
      have same := Result.ok.inj run
      subst xs
      intro e member
      rcases List.mem_cons.mp member with first | tail
      · subst e; exact hp
      · exact ih next rest (XRm_WideProducer.mul _ _ _ hnext) hrest e tail

theorem powers (gamma : XRk_Wide) (scratch : Array XRk_Wide 29#usize)
    (run : weights.powers 29#usize gamma=ok scratch) :
    ∀ e ∈ scratch.val, Canonical e := by
  obtain ⟨one,hone,href⟩ := XRk_PowersAssociation.powers gamma scratch run
  have same := Result.ok.inj hone
  subst one
  exact recurrence gamma 29 _ scratch.val XRm_WideProducer.one href

/-- Accepted actual Prepared.new overwrites scratch with canonical operands.
This is not derived from arbitrary extracted histories or a native-type axiom. -/
theorem prepared {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (old scratch : Array XRk_Wide 29#usize) (out : verifier.Prepared)
    (run : verifier.Prepared.new D sem view hash old=ok (.Ok out,scratch)) :
    ∀ e ∈ scratch.val, Canonical e :=
  powers out.gamma scratch (XRk_ScratchProjection.accepted_powers D sem view hash old scratch out run)

theorem array_read {N : Usize} (a : Array XRk_Wide N) (i : Usize) (out : XRk_Wide)
    (canonical : ∀ e ∈ a.val, Canonical e) (run : Array.index_usize a i=ok out) :
    Canonical out := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i value hread
    have same := Result.ok.inj run
    subst out
    exact canonical _ (List.mem_of_getElem? (by simpa only [Array.getElem?_Usize_eq] using hread))

#print axioms recurrence
#print axioms powers
#print axioms prepared
#print axioms array_read
end XRm_PowersCanonical
