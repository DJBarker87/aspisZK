import Mathlib.Data.List.Range
/-! D157 pure iterator contracts used by encoder::eval_pair. These are
explicit TrustedStd fields, not source arithmetic or caller-image premises.
The model instance witnesses consistency, not a proof of Rust's library. -/
set_option autoImplicit false
namespace R1Z.ProverCommitIteratorStd48
variable {A B : Type}

def exactChunks (xs : List A) (size : Nat) : List (List A) :=
  (List.range (xs.length / size)).map (fun i => (xs.drop (size*i)).take size)

structure API (A B : Type) where
  chunks_exact : List A → Nat → List (List A)
  zip : List (List A) → List B → List (List A × B)

structure TrustedStd (api : API A B) : Prop where
  /-- slice::chunks_exact(n), n>0: disjoint, forward n-sized chunks;
  the trailing remainder is not yielded. No allocation-totality claim. -/
  slice_chunks_exact : ∀ xs n, 0<n → api.chunks_exact xs n=exactChunks xs n
  /-- Iterator::zip: lockstep forward pairing, ending with the shorter side.
  No user callback or arithmetic semantics is included. -/
  iterator_zip : ∀ xs ys, api.zip xs ys=List.zip xs ys

def modelAPI : API A B := ⟨exactChunks,List.zip⟩

theorem model_consistent : TrustedStd (modelAPI (A := A) (B := B)) :=
  ⟨fun _ _ _ => rfl,fun _ _ => rfl⟩

theorem pair_cursor (api : API A B) (trusted : TrustedStd api)
    (xs : List A) (ys : List B) :
    api.zip (api.chunks_exact xs 2) ys=List.zip (exactChunks xs 2) ys := by
  rw [trusted.slice_chunks_exact xs 2 (by decide),trusted.iterator_zip]

/-- Complete forward iteration has exactly min(floor(len/2),len(basis))
steps, without a premise about source evaluation or field values. -/
theorem pair_count (api : API A B) (trusted : TrustedStd api)
    (xs : List A) (ys : List B) :
    (api.zip (api.chunks_exact xs 2) ys).length=min (xs.length/2) ys.length := by
  rw [pair_cursor api trusted]
  simp only [List.length_zip,exactChunks,List.length_map,List.length_range]

#print axioms model_consistent
#print axioms pair_cursor
#print axioms pair_count
end R1Z.ProverCommitIteratorStd48
