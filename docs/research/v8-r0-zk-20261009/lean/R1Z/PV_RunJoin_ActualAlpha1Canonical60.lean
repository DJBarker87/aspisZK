import R1Z.PV_RunJoin_ActualRun59
import R1Z.PV_RunJoin_ActualAlpha1Trace60
import R1Z.PV_RunJoin_ScalarSuccess49
import R1Z.PV_RunJoin_ScalarRaw50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualAlpha1Canonical60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open ProverCommitWideOps48

theorem zero : canonical (PV_RunJoin_ActualData59.rawW PV_RunJoin_ActualData59.zeroW) :=
  ⟨ProverCommitSubfieldOps47.zero_canonical,ProverCommitSubfieldOps47.zero_canonical⟩

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (phase : @PV_RunJoin_NativeControl55.Phase (types base)) :
    canonical (@PV_RunJoin_ActualRun.data (types base) (selected base heap box ops) phase).b := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  change canonical (PV_RunJoin_ActualData59.finalScalar phase)
  unfold PV_RunJoin_ActualData59.finalScalar
  cases h : PV_RunJoin_ActualRunSources59.alpha1 phase with
  | fail e => exact zero
  | div => exact zero
  | ok status =>
    cases status with
    | none => exact zero
    | some w =>
      obtain ⟨tr,next,payload,hs⟩ := PV_RunJoin_ActualAlpha1Trace60.source phase w h
      obtain ⟨block,a,_,ha,he,_⟩ := PV_RunJoin_ScalarSuccess49.complete
        base heap box ops aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        tr 30#u8 payload false w next hs
      rw [he]
      change canonical (PV_RunJoin_ScalarRaw50.raw (ProverRwDictionaryTower.fromW (source a)))
      rw [PV_RunJoin_ScalarRaw50.roundtrip]
      exact ha

#print axioms zero
#print axioms complete
end R1Z.PV_RunJoin_ActualAlpha1Canonical60
