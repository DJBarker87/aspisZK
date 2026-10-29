import R1Z.PV_RunJoin_WeightInstalled46
import R1Z.PV_RunJoin_CircleInstalled52
import R1Z.PV_DL_EncoderSelected
import R1Z.ProverRwP7FibreInstall
import R1Z.ProverRwP7TraceCloneInstall
import R1Z.PV_TraceValueSource
import R1Z.PV_CB_Op229Source
import PV_B3_Install117
import PV_B3_Install121
import PV_B3_Install222
import PV_B3_Close134
import PV_B3P_Install133
import PV_B3P_Install226V3
import PV_B1_ActualInstall
/-! Adopted dictionary correction. The neutral circle callback is identified
with CircleSelected/nativeCircle by CircleBinding62.native_binding, audited
separately to respect the generated Types collision. V265 retains its
structural-gate qualification. OPEN callbacks are preserved, never assumed. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeResidual62
open Aeneas Aeneas.Std Result ProverRwFull
abbrev baseTypes (base : ExternalTypes) :=
  PV_CBM_MasksSelection.Types (PV_B3P_Install226V3.Types base)
abbrev types (base : ExternalTypes) := PV_RunJoin_WeightInstalled46.types (baseTypes base)

/-- Transport of the existing extracted late-statement equality to the public
serializer's concrete afterstate carrier. Both records have the same fields. -/
def late (base : ExternalTypes)
    (p : @aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 (types base)) :
    PV_CB_Op229Transport.SourceLate :=
  ⟨PV_CB_Op229Transport.snapshot p.live_snapshot,
    ⟨p.candidate_afterstate.next_pair_index,p.candidate_afterstate.next_root,
      p.candidate_afterstate.next_frontier⟩⟩

def residual (base : ExternalTypes) (ops : @ExternalFuns (types base)) : @ExternalFuns (types base) :=
  letI : ExternalTypes := types base
  PV_RunJoin_CircleNeutralSelected52.selected {ops with
    op78 := @ProverRwP7FibreSource.fibre,
    op79 := (PV_DL_EncoderSelected.selected ops).op79,
    op117 := (PV_B3_Install117.selected ops).op117,
    op121 := (PV_B3_Install121.selected ops).op121,
    op133 := (PV_B3P_Install133.selected (types base) ops).op133,
    op134 := ok (.Ok PV_Op134_Masks.masks),
    op222 := (PV_B3_Install222.selected ops).op222,
    op226 := (PV_B3P_Install226V3.selected
      (PV_RunJoin_WeightInstalled46.types (PV_CBM_MasksSelection.Types base)) ops).op226,
    op229 := fun a b => PV_CB_Op229Source.source (late base a) (late base b),
    op230 := (PV_B1_ActualInstall.selected ops).op230,
    op231 := fun x => ok x,
    op247 := PV_TraceValueSource.trace.value,
    op254 := (PV_B1_ActualInstall.selected ops).op254}

/-- Existing installations composed onto the residual dictionary. -/
def opsNative (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    @ExternalFuns (types base) :=
  PV_RunJoin_WeightInstalled46.selected (baseTypes base) heap box (residual base ops)

#print axioms baseTypes
#print axioms types
#print axioms late
#print axioms residual
#print axioms opsNative
end R1Z.PV_RunJoin_NativeResidual62
