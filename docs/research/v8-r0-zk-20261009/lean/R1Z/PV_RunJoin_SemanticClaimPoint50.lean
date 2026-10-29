import R1Z.PV_RunJoin_SemanticEmbed50
import R1Z.PV_RunJoin_SemanticPoints50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticClaimPoint50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open PV_RunJoin_SemanticPoints50 (Points read)
def x (a : Points) : Old.Q := ProverCommitNativeOps47.normalize (PV_RunJoin_SemanticScalar50.raw (read a 1).x)
def y (a : Points) : Old.Q := ProverCommitNativeOps47.normalize (PV_RunJoin_SemanticScalar50.raw (read a 1).y)
def point (a : Points) : aspis_core.r0.domain.Point aspis_core.field.wide_exact.WideExact :=
  ⟨ProverRwDictionaryTower.fromW (ProverCommitNativeOps47.embedded (x a)),
   ProverRwDictionaryTower.fromW (ProverCommitNativeOps47.embedded (y a))⟩

def run (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) (a : Points) := do
  let scp ← Array.index_usize a 1#usize
  let x ← @aspis_core.field.wide_exact.WideExact.from_qm31 (types base) (selected base heap box ops) scp.x
  let y ← @aspis_core.field.wide_exact.WideExact.from_qm31 (types base) (selected base heap box ops) scp.y
  ok (aspis_core.r0.domain.Point.mk x y)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) (a : Points) :
    run base heap box ops a=ok (point a) := by
  unfold run
  rw [PV_RunJoin_SemanticPoints50.index a 1#usize (by decide)]
  simp only [bind_tc_ok,PV_RunJoin_SemanticEmbed50.complete]
  rfl

theorem canonical (a : Points) : Canonical (x a) ∧ Canonical (y a) :=
  ⟨ProverCommitNativeOps47.normalize_canonical _,ProverCommitNativeOps47.normalize_canonical _⟩

theorem x_decode (a : Points) : AspisR1.ExtractedCurrentQM31Exact.decode (x a)=
    AspisR1.ExtractedCurrentQM31Exact.decode (PV_RunJoin_SemanticScalar50.raw (read a 1).x) :=
  ProverCommitNativeOps47.normalize_decode _
theorem y_decode (a : Points) : AspisR1.ExtractedCurrentQM31Exact.decode (y a)=
    AspisR1.ExtractedCurrentQM31Exact.decode (PV_RunJoin_SemanticScalar50.raw (read a 1).y) :=
  ProverCommitNativeOps47.normalize_decode _
#print axioms x
#print axioms y
#print axioms point
#print axioms run
#print axioms complete
#print axioms canonical
#print axioms x_decode
#print axioms y_decode
end R1Z.PV_RunJoin_SemanticClaimPoint50
