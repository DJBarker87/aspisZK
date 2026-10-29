import R1Z.PV_RunJoin_ClaimPolynomial49
import R1Z.PV_RunJoin_ClaimStreamCongruence49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimPolynomialStream50
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitWideOps48
open AspisR1.ExtractedCurrentQM31Exact (decode)

def sourceCell (c : Nat → Nat → Old.Q) (x y : Old.Q) (l : Nat) : List UInt8 :=
  List.ofFn (ProverCommitValueRange47.bytes
    (ProverCommitY1Bytes47.model (fun j => c l (AspisR1.rowNat j)) x y))
def modelValue (c : Nat → Nat → Old.Q) (z : AspisR0.ChordGeometry.Point Exact)
    (l : Fin 29) : Exact :=
  AspisR0.Chord.evalMessage (R0P.SemSource.coeffsOf AspisR1.rowEquiv
    (PV_RunJoin_ClaimPolynomial49.trace c) l) z
attribute [local irreducible] modelValue

def modelCell (c : Nat → Nat → Old.Q)
    (z : AspisR0.ChordGeometry.Point Exact) (l : Nat) : List UInt8 :=
  if hl : l<29 then List.ofFn (ProverCommitValueRange47.bytes
    (modelValue c z ⟨l,hl⟩)) else []
attribute [local irreducible] ProverCommitY1Bytes47.model AspisR0.Chord.evalMessage
  R0P.SemSource.coeffsOf PV_RunJoin_ClaimPolynomial49.trace ProverCommitValueRange47.bytes

theorem cell (c : Nat → Nat → Old.Q) (x y : Old.Q)
    (z : AspisR0.ChordGeometry.Point Exact)
    (hx : ProverCommitValueRange47.embed (decode x)=z.1.1)
    (hy : ProverCommitValueRange47.embed (decode y)=z.1.2)
    (l : Nat) (hl : l<29) : sourceCell c x y l=modelCell c z l := by
  unfold sourceCell modelCell
  simp only [modelValue]
  rw [dif_pos hl]
  exact congrArg (fun v => List.ofFn (ProverCommitValueRange47.bytes v))
    (PV_RunJoin_ClaimPolynomial49.message c ⟨l,hl⟩ x y z hx hy)
attribute [local irreducible] sourceCell modelCell

theorem complete (c : Nat → Nat → Old.Q) (x y : Old.Q)
    (z : AspisR0.ChordGeometry.Point Exact)
    (hx : ProverCommitValueRange47.embed (decode x)=z.1.1)
    (hy : ProverCommitValueRange47.embed (decode y)=z.1.2) (start n : Nat)
    (bound : start+n≤29) :
    PV_RunJoin_ClaimImageList49.stream (sourceCell c x y) start n=
      PV_RunJoin_ClaimImageList49.stream (modelCell c z) start n :=
  PV_RunJoin_ClaimStreamCongruence49.complete _ _ (cell c x y z hx hy) start n bound
#print axioms sourceCell
#print axioms modelCell
#print axioms cell
#print axioms complete
end R1Z.PV_RunJoin_ClaimPolynomialStream50
