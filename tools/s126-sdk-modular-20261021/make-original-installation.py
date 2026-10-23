#!/usr/bin/env python3
from pathlib import Path
R=Path(__file__).resolve().parents[2];O=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
s='''import CurrentOriginalPreparedCarrierTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisR1CurrentCaller.OriginalPreparedInstallation
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open AspisR1ClaimPreparedBridge.InstalledMeaning AspisR1CurrentPreparedClaim.Concrete
open AspisR1PreparedSourcePowersBoundariesV1 AspisR1PreparedSourcePowersJointRankV1

def originalNew (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE)
    {H : Type} (D : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    Result ((core.result.Result verifier.Prepared verifier.Error) × Array aspis_core.field.wide_exact.WideExact 29#usize) :=
  OriginalPreparedSource.prepare (sourceBoundaries (installedBoundaries sampling embed)) D sem v hash g

/-- No output/success/totality premise: complete current original source body
under the explicitly installed primitive children equals the retained backend.
The original prepared_claim and RustStd child contracts remain separate gates. -/
theorem originalNew_eq_sourcePrepared
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE) :
    @originalNew sampling embed=@sourcePrepared sampling embed := by
  funext H D sem v hash g
  unfold originalNew
  rw [OriginalPreparedSource.prepare_transport]
  unfold OriginalPreparedSource.transported sourcePrepared
  rw [AspisR1PublicPreparation.OriginalPreparedNative.eq_prepare]
  rfl

def installOriginal (ops : Ops)
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE) : Ops :=
  {InstalledPreparation.install ops sampling embed with op8:=originalNew sampling embed}

theorem installOriginal_eq (ops : Ops)
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE) :
    installOriginal ops sampling embed=InstalledPreparation.install ops sampling embed := by
  unfold installOriginal InstalledPreparation.install
  rw [originalNew_eq_sourcePrepared]

'''
old=(O/'CurrentCompactInstalledPreparationV1.lean').read_text();a=old.index('theorem first_installed_claim_and_rank');b=old.index(' := by',a);stmt=old[a:b].replace('first_installed_claim_and_rank','first_original_new_claim_and_rank').replace('install ops sampling embed','installOriginal ops sampling embed')
s+='''/-- Enclosing first success with the freshly emitted original Prepared.new
body installed on its complete current carriers. The desired claim/rank,
View parsing, decoder result, semantic result and scratch are conclusions.
Primitive child installation is tracked explicitly, never hidden by renaming. -/
'''+stmt+''' := by
  rw [installOriginal_eq] at h ⊢
  exact InstalledPreparation.first_installed_claim_and_rank invalidAccountData ops sampling embed
    D p pubInput root length error bytes proof k out h

#print axioms originalNew_eq_sourcePrepared
#print axioms installOriginal_eq
#print axioms first_original_new_claim_and_rank
end AspisR1CurrentCaller.OriginalPreparedInstallation
'''
(O/'CurrentOriginalPreparedInstallationV1.lean').write_text(s)
