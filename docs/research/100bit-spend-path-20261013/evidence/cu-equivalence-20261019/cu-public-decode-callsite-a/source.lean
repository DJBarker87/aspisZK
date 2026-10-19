import CuSavingsPublicDecodeOrder

/-! Consume both boxed-decoder and argument-order facts in one complete actual
source call-site replacement. The common context includes adapter validation
and checkpoint effects; argument construction may itself fail or diverge. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsPublicDecodeCallsite
open Aeneas Aeneas.Std Result
open CuSavingsPublicDecode CuSavingsPublicDecodeSource CuSavingsPublicDecodeClosed
open CuSavingsPublicDecodeTransfer CuSavingsPublicDecodeOrder
abbrev Arguments := Slice U8 × Usize

def reference {E F A : Type}
    (invalid : E) (tx1 : Tx1 F) (error : F → Result E) (bytes : Slice U8) (obs : Observer)
    (reject : E → Result A) (arguments : ActualStatement → Result Arguments)
    (context : ActualStatement → Result (core.result.Result (alloc.vec.Vec U8) E) → Result A) : Result A := do
  let r ← boxedSource (actualBoundaries tx1 error) invalid bytes
  match r with
  | .Err e => reject e
  | .Ok statement => context statement (do
      let args ← arguments statement
      sourceFirst (actualBoundaries tx1 error) invalid bytes args.1 args.2 obs)

def optimized {E F A : Type}
    (invalid : E) (tx1 : Tx1 F) (error : F → Result E) (bytes : Slice U8) (obs : Observer)
    (reject : E → Result A) (arguments : ActualStatement → Result Arguments)
    (context : ActualStatement → Result (core.result.Result (alloc.vec.Vec U8) E) → Result A) : Result A := do
  let r ← boxedSource (actualBoundaries tx1 error) invalid bytes
  match r with
  | .Err e => reject e
  | .Ok statement => context statement (do
      let pub ← selectActual statement
      let args ← arguments statement
      sourceDecoded (actualBoundaries tx1 error) pub bytes args.1 args.2 obs)

theorem source_eq {E F A : Type}
    (invalid : E) (tx1 : Tx1 F) (error : F → Result E) (bytes : Slice U8) (obs : Observer)
    (reject : E → Result A) (arguments : ActualStatement → Result Arguments)
    (context : ActualStatement → Result (core.result.Result (alloc.vec.Vec U8) E) → Result A) :
    reference invalid tx1 error bytes obs reject arguments context =
      optimized invalid tx1 error bytes obs reject arguments context := by
  unfold reference optimized
  simp only [boxed_eq,decodeBox]
  cases hd : (actualBoundaries tx1 error).decode bytes with
  | fail e => rfl
  | div => rfl
  | ok r =>
    cases r with
    | Err e => rfl
    | Ok statement =>
      have hbox : boxedSource (actualBoundaries tx1 error) invalid bytes = .ok (.Ok statement) := by
        simp only [boxed_eq,decodeBox,hd,bind_tc_ok]
      obtain ⟨pub,hpub⟩ := select_after_box invalid tx1 error bytes statement hbox
      have hs : (actualBoundaries tx1 error).select statement = .ok pub := hpub
      simp only [bind_tc_ok,hpub]
      apply congrArg (context statement)
      apply (bind_eq_iff (arguments statement) _ _).mpr
      intro args _
      rw [source_first_of_decode (actualBoundaries tx1 error) invalid bytes args.1 args.2 obs statement hd]
      simp only [hs,bind_tc_ok]

theorem observations_eq {E F A Observation : Type}
    (invalid : E) (tx1 : Tx1 F) (error : F → Result E) (bytes : Slice U8) (obs : Observer)
    (reject : E → Result A) (arguments : ActualStatement → Result Arguments)
    (context : ActualStatement → Result (core.result.Result (alloc.vec.Vec U8) E) → Result A)
    (observe : Result A → Observation) :
    observe (reference invalid tx1 error bytes obs reject arguments context) =
      observe (optimized invalid tx1 error bytes obs reject arguments context) :=
  congrArg observe (source_eq invalid tx1 error bytes obs reject arguments context)

#print axioms reference
#print axioms optimized
#print axioms source_eq
#print axioms observations_eq
end AspisR1.CuSavingsPublicDecodeCallsite
