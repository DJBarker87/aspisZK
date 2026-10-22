import R1Z.ProverCommitNativePair48
import R1Z.ProverCommitY1Bytes47
/-! P6 evaluator denotation: nine native basis stages, followed by all 512
pair iterations. Primitive arithmetic and pointwise bytes are inherited from
part 47. The simulator's coefficient/tape provenance is a separate boundary. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitNativeEval48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact
abbrev E := field.wide_exact.WideExact

def basis (x : E) : Result (Array E 512#usize) :=
  ProverCommitBasisCounter47.stagesN 9
    (Array.repeat 512#usize field.wide_exact.WideExact.ONE) 1#usize x

theorem basis_owner (x : E) : basis x=values x := by
  exact (ProverCommitBasisCounter47.values_counter x).symm

def run (q : Nat → Old.Q) (x y : Old.Q) : Result E := do
  let b ← basis (ProverCommitNativeOps47.embedded x)
  ProverCommitNativePair48.evaluate (ProverCommitPairCounter47.sourceArray 1024#usize q) b
    (ProverCommitNativeOps47.embedded y)

theorem run_owner (q : Nat → Old.Q) (x y : Old.Q) : run q x y=ProverCommitY1Owner47.run q x y := by
  simp only [run,ProverCommitY1Owner47.run,basis_owner,ProverCommitNativePair48.evaluate_owner]

theorem raw_value (q : Nat → Old.Q) (x y : Old.Q) :
    ∃ z : Old.Q,
      run (fun j => ProverCommitNativeOps47.normalize (q j))
        (ProverCommitNativeOps47.normalize x) (ProverCommitNativeOps47.normalize y) =
          ok (ProverCommitNativeOps47.embedded z) ∧ Canonical z ∧
      decode z=ProverCommitEval47.messageEval
        (fun j : Fin 1024 => decode (q j.val)) (decode x) (decode y) := by
  rw [run_owner]
  exact ProverCommitY1Owner47.raw_value q x y

theorem bytes (q : Nat → Old.Q) (x y : Old.Q) :
    ∃ (z : Old.Q) (hz : Canonical z),
      run (fun j => ProverCommitNativeOps47.normalize (q j))
        (ProverCommitNativeOps47.normalize x) (ProverCommitNativeOps47.normalize y) =
          ok (ProverCommitNativeOps47.embedded z) ∧
      ProverCommitLimbBytes47.sourceCell z hz=ProverCommitValueRange47.bytes (ProverCommitY1Bytes47.model q x y) ∧
      AspisR1.FoldedLeafCodec.decodeWide
        ((List.ofFn (ProverCommitLimbBytes47.sourceCell z hz)).map UInt8.toFin)=
          some (ProverCommitY1Bytes47.model q x y) := by
  rw [run_owner]
  exact ProverCommitY1Bytes47.component q x y

#print axioms basis_owner
#print axioms run_owner
#print axioms raw_value
#print axioms bytes
end R1Z.ProverCommitNativeEval48
