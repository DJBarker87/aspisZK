import CuSavingsPublicDecode
import ExtractedFirstCallerReachability

/-! Bind the prior complete emitted first control flow to the decode-reuse
model. Boundary carriers and functions are universally quantified; no law of
an unchanged decoder or tx1 is postulated. The source audit checks the complete
body against ExtractedFirstCallerReachability after these explicit bindings.
The new first_decoded body is the old tx1/map_err suffix, factored unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsPublicDecodeSource
open Aeneas Aeneas.Std Result
open CuSavingsPublicDecode

def decodeErrorClosure {D E : Type} (invalid : E) :
    core.ops.function.FnOnce Unit D E :=
  {call_once := fun _ _ => .ok invalid}

def sourceDecoded {S P D E F O Obs : Type} (B : Boundaries S P D E F O Obs)
    (pub : P) (bytes proof : Slice U8) (k : Usize) (obs : Obs) :
    Result (core.result.Result O E) := do
  let result ← B.tx1 pub bytes proof k obs
  AspisR1PublicPreparation.core.result.Result.map_err (BuiltinFnOnce F E) result B.error

/-- Complete historical first body with explicit shared boundary bindings.
The sole observer expression is a parameter, so this candidate is independent
of the separately required observer/log-projection proof. -/
def sourceFirst {S P D E F O Obs : Type} (B : Boundaries S P D E F O Obs)
    (invalid : E) (bytes proof : Slice U8) (k : Usize) (obs : Obs) :
    Result (core.result.Result O E) := do
  let r ← B.decode bytes
  let r1 ← AspisR1PublicPreparation.core.result.Result.map_err (decodeErrorClosure invalid) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let public1 ← B.select val
    let r2 ← B.tx1 public1 bytes proof k obs
    AspisR1PublicPreparation.core.result.Result.map_err (BuiltinFnOnce F E) r2 B.error
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      O (core.convert.FromSame E) residual

theorem map_error_eq {A E F : Type} (f : F → Result E)
    (value : core.result.Result A F) :
    AspisR1PublicPreparation.core.result.Result.map_err (BuiltinFnOnce F E) value f = mapError f value := by
  cases value <;> rfl

theorem source_decoded_eq {S P D E F O Obs : Type} (B : Boundaries S P D E F O Obs)
    (pub : P) (bytes proof : Slice U8) (k : Usize) (obs : Obs) :
    sourceDecoded B pub bytes proof k obs = firstDecoded B pub bytes proof k obs := by
  simp only [sourceDecoded,firstDecoded,map_error_eq]

theorem source_first_eq {S P D E F O Obs : Type} (B : Boundaries S P D E F O Obs)
    (invalid : E) (bytes proof : Slice U8) (k : Usize) (obs : Obs) :
    sourceFirst B invalid bytes proof k obs = first B invalid bytes proof k obs := by
  unfold sourceFirst first
  cases hd : B.decode bytes with
  | fail e => rfl
  | div => rfl
  | ok result =>
    cases result with
    | Err error =>
      simp only [bind_tc_ok,AspisR1PublicPreparation.core.result.Result.map_err,decodeErrorClosure,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from]
    | Ok statement =>
      simp only [bind_tc_ok,AspisR1PublicPreparation.core.result.Result.map_err,
        core.result.Result.Insts.CoreOpsTry.branch,firstDecoded]
      apply (bind_eq_iff (B.select statement) _ _).mpr
      intro pub _
      apply (bind_eq_iff (B.tx1 pub bytes proof k obs) _ _).mpr
      intro result _
      exact map_error_eq B.error result

theorem source_first_of_decode {S P D E F O Obs : Type}
    (B : Boundaries S P D E F O Obs) (invalid : E)
    (bytes proof : Slice U8) (k : Usize) (obs : Obs) (statement : S)
    (hd : B.decode bytes = .ok (.Ok statement)) :
    sourceFirst B invalid bytes proof k obs = (do
      let pub ← B.select statement
      sourceDecoded B pub bytes proof k obs) := by
  rw [source_first_eq,first_of_decode B invalid bytes proof k obs statement hd]
  simp only [reused,source_decoded_eq]


/-- Fixed actual decoder and selector; only the original downstream boundaries
remain parameters. The source unit-struct digest argument is passed unchanged. -/
def actualBoundaries {E F : Type}
    (tx1 : AspisR1PublicPreparation.FirstCaller.Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (AspisR1PublicPreparation.FirstCaller.Phase → Result Unit) →
      Result (core.result.Result (alloc.vec.Vec U8) F))
    (error : F → Result E) :
    Boundaries AspisR1PublicPreparation.FirstCaller.Statement
      AspisR1PublicPreparation.FirstCaller.Public AspisR1PublicPreparation.FirstCaller.DecodeError
      E F (alloc.vec.Vec U8)
      (Option (AspisR1PublicPreparation.FirstCaller.Phase → Result Unit)) :=
  {decode := AspisR1PublicPreparation.FirstCaller.decode,
   select := AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public,
   tx1 := fun pub bytes proof k obs => tx1 pub bytes proof k () obs,
   error := error}

theorem original_first_eq {E F : Type} (invalid : E)
    (tx1 : AspisR1PublicPreparation.FirstCaller.Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (AspisR1PublicPreparation.FirstCaller.Phase → Result Unit) →
      Result (core.result.Result (alloc.vec.Vec U8) F))
    (mark : AspisR1PublicPreparation.FirstCaller.Phase → Result Unit)
    (error : F → Result E) (bytes proof : Slice U8) (k : Usize) :
    AspisR1PublicPreparation.FirstCaller.first invalid tx1 mark error bytes proof k =
      sourceFirst (actualBoundaries tx1 error) invalid bytes proof k (some mark) := by
  rfl

/-- Whole adapter replacement under the exact original decoder/selector and
caller interpretation. Its earlier decode discharges the repeated-decode
premise. The context may contain all validation and checkpoint operations. -/
theorem actual_adapter_context_eq {E F A : Type} (invalid : E)
    (tx1 : AspisR1PublicPreparation.FirstCaller.Public → Slice U8 → Slice U8 → Usize → Unit →
      Option (AspisR1PublicPreparation.FirstCaller.Phase → Result Unit) →
      Result (core.result.Result (alloc.vec.Vec U8) F))
    (mark : AspisR1PublicPreparation.FirstCaller.Phase → Result Unit)
    (error : F → Result E) (bytes proof : Slice U8) (k : Usize)
    (reject : E → Result A)
    (context : AspisR1PublicPreparation.FirstCaller.Statement →
      Result (core.result.Result (alloc.vec.Vec U8) E) → Result A) :
    (do
      let result ← decodeBox (actualBoundaries tx1 error) invalid bytes
      match result with
      | .Err err => reject err
      | .Ok statement => context statement
          (AspisR1PublicPreparation.FirstCaller.first invalid tx1 mark error bytes proof k)) =
    (do
      let result ← decodeBox (actualBoundaries tx1 error) invalid bytes
      match result with
      | .Err err => reject err
      | .Ok statement => context statement (do
          let pub ← (actualBoundaries tx1 error).select statement
          sourceDecoded (actualBoundaries tx1 error) pub bytes proof k (some mark))) := by
  simp only [original_first_eq,source_first_eq,source_decoded_eq]
  exact adapter_context_eq (actualBoundaries tx1 error) invalid bytes proof k (some mark) reject context

#print axioms decodeErrorClosure
#print axioms sourceDecoded
#print axioms sourceFirst
#print axioms map_error_eq
#print axioms source_decoded_eq
#print axioms source_first_eq
#print axioms source_first_of_decode
#print axioms actualBoundaries
#print axioms original_first_eq
#print axioms actual_adapter_context_eq
end AspisR1.CuSavingsPublicDecodeSource
