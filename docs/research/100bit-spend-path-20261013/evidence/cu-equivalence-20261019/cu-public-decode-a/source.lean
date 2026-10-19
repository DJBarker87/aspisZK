import Aeneas

/-! Public-decode reuse under universally quantified, unchanged source boundaries.
The decoder result is supplied by the earlier adapter decode, not assumed by
an exported context theorem. Selector, tx1 and error-mapper failure/divergence
are preserved. Public bytes are the original bytes in every tx1 call. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsPublicDecode
open Aeneas Aeneas.Std Result

structure Boundaries (Statement Public DecodeError Error TxError Output Observer : Type) where
  decode : Slice U8 → Result (core.result.Result Statement DecodeError)
  select : Statement → Result Public
  tx1 : Public → Slice U8 → Slice U8 → Usize → Observer →
    Result (core.result.Result Output TxError)
  error : TxError → Result Error

def mapError {A E F : Type} (f : F → Result E) :
    core.result.Result A F → Result (core.result.Result A E)
  | .Ok value => .ok (.Ok value)
  | .Err error => do let mapped ← f error; .ok (.Err mapped)

def firstDecoded {S P D E F O Obs : Type} (B : Boundaries S P D E F O Obs)
    (pub : P) (bytes proof : Slice U8) (k : Usize) (obs : Obs) :
    Result (core.result.Result O E) := do
  let result ← B.tx1 pub bytes proof k obs
  mapError B.error result

def first {S P D E F O Obs : Type} (B : Boundaries S P D E F O Obs)
    (invalid : E) (bytes proof : Slice U8) (k : Usize) (obs : Obs) :
    Result (core.result.Result O E) := do
  let result ← B.decode bytes
  match result with
  | .Err _ => .ok (.Err invalid)
  | .Ok statement => do
    let pub ← B.select statement
    firstDecoded B pub bytes proof k obs

/-- Exact observable projection of the shared boxed decoder: map its format
error, retain the same returned statement. Box allocation is interpreted at
its ordinary source-model boundary, with sufficient resources. -/
def decodeBox {S P D E F O Obs : Type} (B : Boundaries S P D E F O Obs)
    (invalid : E) (bytes : Slice U8) : Result (core.result.Result S E) := do
  let result ← B.decode bytes
  match result with
  | .Err _ => .ok (.Err invalid)
  | .Ok statement => .ok (.Ok statement)

def reused {S P D E F O Obs : Type} (B : Boundaries S P D E F O Obs)
    (statement : S) (bytes proof : Slice U8) (k : Usize) (obs : Obs) :
    Result (core.result.Result O E) := do
  let pub ← B.select statement
  firstDecoded B pub bytes proof k obs

theorem first_of_decode {S P D E F O Obs : Type} (B : Boundaries S P D E F O Obs)
    (invalid : E) (bytes proof : Slice U8) (k : Usize) (obs : Obs) (statement : S)
    (hd : B.decode bytes = .ok (.Ok statement)) :
    first B invalid bytes proof k obs = reused B statement bytes proof k obs := by
  simp only [first,hd,bind_tc_ok,reused]

/-- The surrounding adapter can reject before calling tx1 or process its
result arbitrarily. Both controls use exactly the same immutable bytes. There
is no decoder-success, tx1-success or equivalence premise. -/
theorem adapter_context_eq {S P D E F O Obs A : Type}
    (B : Boundaries S P D E F O Obs) (invalid : E)
    (bytes proof : Slice U8) (k : Usize) (obs : Obs)
    (reject : E → Result A)
    (context : S → Result (core.result.Result O E) → Result A) :
    (do
      let result ← decodeBox B invalid bytes
      match result with
      | .Err error => reject error
      | .Ok statement => context statement (first B invalid bytes proof k obs)) =
    (do
      let result ← decodeBox B invalid bytes
      match result with
      | .Err error => reject error
      | .Ok statement => context statement (reused B statement bytes proof k obs)) := by
  unfold decodeBox
  cases hd : B.decode bytes with
  | fail e => rfl
  | div => rfl
  | ok result =>
    cases result with
    | Err error => rfl
    | Ok statement =>
      simp only [bind_tc_ok]
      rw [first_of_decode B invalid bytes proof k obs statement hd]

#print axioms mapError
#print axioms firstDecoded
#print axioms first
#print axioms decodeBox
#print axioms reused
#print axioms first_of_decode
#print axioms adapter_context_eq
end AspisR1.CuSavingsPublicDecode
