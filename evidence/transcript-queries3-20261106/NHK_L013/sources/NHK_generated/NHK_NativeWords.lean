import NHK_WordAssociation
import NHB_Canonical
set_option autoImplicit false
namespace AspisR1.NHK_NativeWords
open Aeneas Aeneas.Std Result
abbrev State := NGQ_SamplerTrace.State

/-- Chronological native cuts on ONE iterator and mutable scan state. Each
continuing edge has the actual membership reply and K053's full window G.
No whole loop result or independently selected final state is a premise. -/
inductive Cuts : Nat → List U32 → State → State → Nat → Option Bool → Prop where
 | exhausted (cursor : Nat) (s : State) : Cuts cursor [] s s cursor (some false)
 | stopped (cursor last : Nat) (x : U32) (xs : List U32) (s after : State) (reply : Bool)
     (full : s.accepted_len.val=22 ∨ s.draws.val=64)
     (windows : ∀ j, NHB_Observation.observe after x last true j = NHK_WordAssociation.G s x cursor reply j) :
     Cuts cursor (x::xs) s after last none
 | continuing (cursor nextCursor last : Nat) (x : U32) (xs : List U32)
     (s after final : State) (pending : Option Bool) (reply : Bool)
     (hlen : s.accepted_len.val<22) (hdraw : s.draws.val<64)
     (value : reply = NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val))
     (windows : ∀ j, NHB_Observation.observe after x nextCursor false j = NHK_WordAssociation.G s x cursor reply j)
     (tail : Cuts nextCursor xs after final last pending) :
     Cuts cursor (x::xs) s final last pending

/-- Rule-B induction on the actual local records; last/final remain the native
observations throughout, rather than being replaced by existential model data. -/
theorem association {cursor last : Nat} {xs : List U32} {s final : State} {pending : Option Bool}
    (cuts : Cuts cursor xs s final last pending) :
    NHB_WordTrace.Trace cursor xs s final last pending := by
  induction cuts with
  | exhausted cursor s => exact .exhausted cursor s
  | stopped cursor last x xs s after reply full windows =>
    obtain ⟨_,hc,ha⟩ := NHK_WordAssociation.stopped_post s after x cursor last true reply full windows
    subst after
    subst last
    have hfull : s.accepted_len=22#usize ∨ s.draws=64#usize := by
      rcases full with hn | hd
      · exact Or.inl (UScalar.eq_of_val_eq hn)
      · exact Or.inr (UScalar.eq_of_val_eq hd)
    exact .stopped cursor x xs s hfull
  | continuing cursor nextCursor last x xs s after final pending reply hlen hdraw value windows tail ih =>
    have observed : NHB_Observation.Relation s after x cursor nextCursor false := by
      intro j
      exact (windows j).trans (NHK_WordAssociation.substitute s x cursor reply value j)
    obtain ⟨_,hc,frame⟩ := NHB_Observation.continuing_frame s after x cursor nextCursor false hlen hdraw observed
    subst nextCursor
    exact .continuing cursor x xs s after final last pending hlen hdraw frame ih

theorem source {cursor last : Nat} {xs : List U32} {s final : State} {pending : Option Bool}
    (cuts : Cuts cursor xs s final last pending) :
    Query31ExplicitListLoop.scanListLoop xs s=ok (final,pending) :=
  NHB_WordTrace.source (association cuts)

theorem domain_preserved {cursor last : Nat} {xs : List U32} {s final : State} {pending : Option Bool}
    (cuts : Cuts cursor xs s final last pending)
    (valid : Query31ExplicitListLoop.validState s)
    (canonical : NHB_Canonical.State s) (inactive : NHB_Inactive.State s)
    (words : ∀ x∈xs,x.val<262144) :
    Query31ExplicitListLoop.validState final ∧ NHB_Canonical.State final ∧ NHB_Inactive.State final := by
  have trace := association cuts
  exact ⟨NHB_Domains.word_invariant trace valid,
    NHB_Canonical.word_invariant trace canonical words,NHB_Inactive.word_invariant trace inactive⟩

#print axioms association
#print axioms source
#print axioms domain_preserved
end AspisR1.NHK_NativeWords
