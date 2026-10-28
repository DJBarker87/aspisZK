import R1Z.PV_RunJoin_FieldData34
import R1Z.ProverCommitWideQM31Scalar49
import R1Z.PV_RunJoin_FlatBytes35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PolyCell38
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev Q := aspis_core.field.QM31

def wide (q : Q) : aspis_core.field.wide_exact.WideExact :=
  ⟨PV_RunJoin_FieldData34.source
    (ProverCommitNativeOps47.normalize (PV_RunJoin_FieldData34.old q)),⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
def cell (q : Q) : List U8 := (PV_RunJoin_FlatBytes35.wire (wide q)).val

theorem embed (ops : ExternalFuns) (q : Q) :
    (ProverRwP6BodyCandidate.selected ops).op45 q = .ok (wide q) := by
  change ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromW
    (AspisR1ProducerRelease47.field.wide_exact.WideExact.from_qm31
      (ProverRwDictionaryTower.toQ q)) = _
  rw [AspisR1ProducerRelease47.field.wide_exact.WideExact.from_qm31,
    ← PV_RunJoin_FieldData34.native_source q,
    ProverCommitWideQM31Scalar49.normalize_source]
  simp only [bind_tc_ok,AspisR1ProducerRelease47.field.QM31.ZERO,
    ProverRwDictionaryTower.mapResult]
  rfl

theorem encode (ops : ExternalFuns) (q : Q) :
    (do
      let w ← @aspis_core.field.wide_exact.WideExact.from_qm31 _
        (ProverRwP6BodyCandidate.selected ops) q
      @aspis_core.field.wide_exact.WideExact.to_le_bytes _
        (ProverRwP6BodyCandidate.selected ops) w) =
      .ok (PV_RunJoin_FlatBytes35.wire (wide q)) := by
  rw [show @aspis_core.field.wide_exact.WideExact.from_qm31 _
      (ProverRwP6BodyCandidate.selected ops) q = .ok (wide q) from embed ops q]
  simp only [bind_tc_ok]
  exact PV_RunJoin_FlatBytes35.installed ops (wide q)

theorem length (q : Q) : (cell q).length = 32 :=
  (PV_RunJoin_FlatBytes35.wire (wide q)).property

#print axioms embed
#print axioms encode
#print axioms length
end R1Z.PV_RunJoin_PolyCell38
