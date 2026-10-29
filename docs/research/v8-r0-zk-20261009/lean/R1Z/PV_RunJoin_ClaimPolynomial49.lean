import R1Z.PV_RunJoin_ClaimStream49
import R1Z.ProverCommitCoefficientModel51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimPolynomial49
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitWideOps48
open AspisR1.ExtractedCurrentQM31Exact (decode)

def trace (c : Nat → Nat → Old.Q) : R0P.Trace Exact :=
  fun l j => ProverCommitValueRange47.embed (decode (c l.val j.val))

theorem coefficient (c : Nat → Nat → Old.Q) (l : Fin 29) (j : Fin 1024) :
    R0P.SemSource.coeffsOf AspisR1.rowEquiv (trace c) l j=
      ProverCommitValueRange47.embed (decode (c l.val (AspisR1.rowNat j.val))) := by
  change ProverCommitValueRange47.embed (decode (c l.val (AspisR1.rowEquiv.symm j).val))=_
  rw [←ProverCommitCoefficientModel51.row j]

theorem message (c : Nat → Nat → Old.Q) (l : Fin 29) (x y : Old.Q)
    (z : AspisR0.ChordGeometry.Point Exact)
    (hx : ProverCommitValueRange47.embed (decode x)=z.1.1)
    (hy : ProverCommitValueRange47.embed (decode y)=z.1.2) :
    ProverCommitY1Bytes47.model (fun j => c l.val (AspisR1.rowNat j)) x y=
      AspisR0.Chord.evalMessage (R0P.SemSource.coeffsOf AspisR1.rowEquiv (trace c) l) z := by
  unfold ProverCommitY1Bytes47.model
  rw [hx,hy]
  have eq : R0P.SemSource.coeffsOf AspisR1.rowEquiv (trace c) l=
      (fun j : Fin 1024 => ProverCommitValueRange47.embed (decode (c l.val (AspisR1.rowNat j.val)))) :=
    funext (coefficient c l)
  rw [←eq]
  exact ProverCommitEval47.message_model _ z
#print axioms trace
#print axioms coefficient
#print axioms message
end R1Z.PV_RunJoin_ClaimPolynomial49
