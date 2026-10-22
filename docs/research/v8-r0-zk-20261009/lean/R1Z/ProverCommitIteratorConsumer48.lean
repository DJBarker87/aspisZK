import Mathlib.Data.List.Basic
/-! D157 pure consumers used by host_semantic::extra and prover::encoded.
Callback arithmetic/value laws are separate verified callee obligations. -/
set_option autoImplicit false
namespace R1Z.ProverCommitIteratorConsumer48
variable {A S B : Type}

structure API (A S B : Type) where
  reverse : List A → List A
  fold : (S → A → S) → S → List A → S
  flatMap : (A → List B) → List A → List B

structure TrustedStd (api : API A S B) : Prop where
  iterator_rev : ∀ xs, api.reverse xs=xs.reverse
  iterator_fold : ∀ f initial xs, api.fold f initial xs=xs.foldl f initial
  iterator_flat_map : ∀ f xs, api.flatMap f xs=(xs.map f).flatten

def modelAPI : API A S B := ⟨List.reverse,List.foldl,fun f xs => (xs.map f).flatten⟩

theorem model_consistent : TrustedStd (modelAPI (A := A) (S := S) (B := B)) :=
  ⟨fun _ => rfl,fun _ _ _ => rfl,fun _ _ => rfl⟩

theorem reverse_fold (api : API A S B) (trusted : TrustedStd api)
    (f : S → A → S) (initial : S) (xs : List A) :
    api.fold f initial (api.reverse xs)=xs.reverse.foldl f initial := by
  rw [trusted.iterator_rev,trusted.iterator_fold]

/-- Complete serialization order, not merely equality of the byte multiset.
This law says nothing about the primitive serializer's field meaning. -/
theorem encoded (api : API A S B) (trusted : TrustedStd api)
    (bytes : A → List B) (values : List A) :
    api.flatMap bytes values=(values.map bytes).flatten := trusted.iterator_flat_map bytes values

#print axioms model_consistent
#print axioms reverse_fold
#print axioms encoded
end R1Z.ProverCommitIteratorConsumer48
