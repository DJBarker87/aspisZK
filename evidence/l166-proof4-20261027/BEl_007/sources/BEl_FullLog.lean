import BEl_LogCoordinates
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_FullLog
open Aeneas Aeneas.Std Result SdkC_Source

/-- Exact nested byte carrier used by the owned recorder, before encoding
back to Aeneas slice refinements. Lengths distinguish empty from absent parts. -/
structure Record (Byte Reply : Type) where
  input : List (List Byte)
  returned : Reply

/-- Part lengths plus every byte coordinate reconstruct one complete input. -/
theorem parts_ext {Byte : Type} (left right : List (List Byte))
    (lengths : left.map List.length = right.map List.length)
    (bytes : ∀ (i j : Nat), (left[i]?).bind (fun p => p[j]?) =
      (right[i]?).bind (fun p => p[j]?)) : left = right := by
  apply List.ext_getElem?
  intro i
  have present := congrArg (fun sizes => sizes[i]?) lengths
  simp only [List.getElem?_map] at present
  cases a : left[i]? with
  | none =>
    cases b : right[i]? with
    | none => rfl
    | some y => simp only [a,b,Option.map_none,Option.map_some] at present; cases present
  | some x =>
    cases b : right[i]? with
    | none => simp only [a,b,Option.map_none,Option.map_some] at present; cases present
    | some y =>
      congr 1
      apply List.ext_getElem?
      intro j
      simpa only [a,b,Option.bind_some] using bytes i j

/-- Full record equality; ordered parts and returned values are retained. -/
theorem record_ext {Byte Reply : Type} (left right : Record Byte Reply)
    (lengths : left.input.map List.length = right.input.map List.length)
    (bytes : ∀ (i j : Nat), (left.input[i]?).bind (fun p => p[j]?) =
      (right.input[i]?).bind (fun p => p[j]?))
    (returned : left.returned = right.returned) : left = right := by
  have inputs := parts_ext left.input right.input lengths bytes
  cases left
  cases right
  simp only [Record.mk.injEq] at *
  exact ⟨inputs,returned⟩

#print axioms parts_ext
#print axioms record_ext
end AspisR1.BEl_FullLog
end
