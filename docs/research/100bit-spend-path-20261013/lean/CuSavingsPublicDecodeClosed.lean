import CuSavingsPublicDecodePreparation

/-! Candidate 6, with other changes fixed. The complete emitted boxed wrapper
is interpreted parametrically, then bound to the actual reference decoder and
selector. All surrounding adapter behavior is a common context. Box projection
uses the original Aeneas primitive, not a new correspondence premise. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsPublicDecodeClosed
open Aeneas Aeneas.Std Result
open CuSavingsPublicDecode CuSavingsPublicDecodeSource

def boxedSource {S P D E F O Obs : Type} (B : Boundaries S P D E F O Obs)
    (invalid : E) (bytes : Slice U8) : Result (core.result.Result S E) := do
  let r ← B.decode bytes
  let r1 ← AspisR1PublicPreparation.core.result.Result.map_err (decodeErrorClosure invalid) r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | .Continue statement => .ok (.Ok statement)
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      S (core.convert.FromSame E) residual

theorem boxed_eq {S P D E F O Obs : Type} (B : Boundaries S P D E F O Obs)
    (invalid : E) (bytes : Slice U8) : boxedSource B invalid bytes = decodeBox B invalid bytes := by
  unfold boxedSource decodeBox
  cases B.decode bytes with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

theorem projection_eq {S : Type} (statement : S) :
    alloc.boxed.Box.deref statement = statement := rfl

def referenceAdapter {S P D E F O Obs A : Type}
    (B : Boundaries S P D E F O Obs) (invalid : E)
    (bytes proof : Slice U8) (k : Usize) (obs : Obs)
    (reject : E → Result A)
    (context : S → Result (core.result.Result O E) → Result A) : Result A := do
  let result ← boxedSource B invalid bytes
  match result with
  | .Err error => reject error
  | .Ok statement => context statement (sourceFirst B invalid bytes proof k obs)

def optimizedAdapter {S P D E F O Obs A : Type}
    (B : Boundaries S P D E F O Obs) (invalid : E)
    (bytes proof : Slice U8) (k : Usize) (obs : Obs)
    (reject : E → Result A)
    (context : S → Result (core.result.Result O E) → Result A) : Result A := do
  let result ← boxedSource B invalid bytes
  match result with
  | .Err error => reject error
  | .Ok statement => context statement (do
      let pub ← B.select (alloc.boxed.Box.deref statement)
      sourceDecoded B pub bytes proof k obs)

/-- Full contextual equality, including returned state/effects when carried in
A. No decoder-success, selector-success, tx1-success or equivalence premise. -/
theorem adapter_eq {S P D E F O Obs A : Type}
    (B : Boundaries S P D E F O Obs) (invalid : E)
    (bytes proof : Slice U8) (k : Usize) (obs : Obs)
    (reject : E → Result A)
    (context : S → Result (core.result.Result O E) → Result A) :
    referenceAdapter B invalid bytes proof k obs reject context =
      optimizedAdapter B invalid bytes proof k obs reject context := by
  simp only [referenceAdapter,optimizedAdapter,boxed_eq,projection_eq]
  exact CuSavingsPublicDecodeTransfer.source_adapter_context_eq B invalid bytes proof k obs reject context

/-- Any observation of the complete adapter result is preserved; error,
divergence and successful byte/state/effect outputs are not discarded. -/
theorem observations_eq {S P D E F O Obs A Observation : Type}
    (B : Boundaries S P D E F O Obs) (invalid : E)
    (bytes proof : Slice U8) (k : Usize) (obs : Obs)
    (reject : E → Result A)
    (context : S → Result (core.result.Result O E) → Result A)
    (observe : Result A → Observation) :
    observe (referenceAdapter B invalid bytes proof k obs reject context) =
      observe (optimizedAdapter B invalid bytes proof k obs reject context) :=
  congrArg observe (adapter_eq B invalid bytes proof k obs reject context)

/-- Transfer any existing reference contract, without supplying a new
optimization-equivalence premise. This includes acceptance-to-formatting and
terminal rejection contracts at the unchanged reference boundary. -/
theorem transfer_contract {S P D E F O Obs A : Type}
    (B : Boundaries S P D E F O Obs) (invalid : E)
    (bytes proof : Slice U8) (k : Usize) (obs : Obs)
    (reject : E → Result A)
    (context : S → Result (core.result.Result O E) → Result A)
    (contract : Result A → Prop)
    (reference_contract : contract (referenceAdapter B invalid bytes proof k obs reject context)) :
    contract (optimizedAdapter B invalid bytes proof k obs reject context) := by
  rw [←adapter_eq B invalid bytes proof k obs reject context]
  exact reference_contract

/-- Fix the actual reference decoder and selector, retaining precisely its
unchanged downstream and enclosing-runtime/context parameters. -/
theorem actual_adapter_eq {E F A : Type}
    (invalid : E) (tx1 : CuSavingsPublicDecodeTransfer.Tx1 F) (error : F → Result E)
    (bytes proof : Slice U8) (k : Usize) (obs : CuSavingsPublicDecodeTransfer.Observer)
    (reject : E → Result A)
    (context : CuSavingsPublicDecodeTransfer.ActualStatement →
      Result (core.result.Result (alloc.vec.Vec U8) E) → Result A) :
    referenceAdapter (actualBoundaries tx1 error) invalid bytes proof k obs reject context =
      optimizedAdapter (actualBoundaries tx1 error) invalid bytes proof k obs reject context :=
  adapter_eq (actualBoundaries tx1 error) invalid bytes proof k obs reject context

#print axioms boxedSource
#print axioms boxed_eq
#print axioms projection_eq
#print axioms referenceAdapter
#print axioms optimizedAdapter
#print axioms adapter_eq
#print axioms observations_eq
#print axioms transfer_contract
#print axioms actual_adapter_eq
#print axioms AspisR1.CuSavingsPublicDecodeTransfer.entry_success
#print axioms AspisR1.CuSavingsPublicDecodePreparation.entry_helper_parsePublic
end AspisR1.CuSavingsPublicDecodeClosed
