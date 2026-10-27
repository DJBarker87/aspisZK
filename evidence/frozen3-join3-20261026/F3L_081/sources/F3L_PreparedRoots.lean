import F3L_SourcePrepared
import SdkD_PhysicalRoots
import SdkD_RootBinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_PreparedRoots
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open MultiproofConeCanonical OraclePortCompactDraft OraclePortBatchDraft

theorem roots (ops : Ops) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (proof : Slice U8) (hash : Hash)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std) D pub proof hash none input=
      ok (.Ok (currentPrepared out),scratch))
    (stored : Bytes) (p : Parsed) (parsed : parse stored=some p) (wire : p.wire=bytesOf proof.val) :
    (F3L_SourcePrepared.numeric out).roots=(fun j=>committedRoot p j.val) := by
  obtain ⟨r0,r1,roots,physical0,physical1⟩ := SdkD_PhysicalRoots.prepared ops B std D pub proof hash
    (currentPrepared out) input scratch prepare
  have b0 : bytesOf r0.val=slice p.wire 16 32 := by
    rw [physical0,SdkD_ModelRoots.rawSlice,wire]
  have b1 : bytesOf r1.val=slice p.wire 63 32 := by
    rw [physical1,SdkD_ModelRoots.rawSlice,wire]
  have model0 := SdkD_RootBinding.root0 p r0 b0
  have model1 := SdkD_RootBinding.root1 stored p parsed r1 b1
  have original : out.roots=Array.make 2#usize [r0,r1] := roots
  funext j
  fin_cases j
  · change decodeState (out.roots.val[0]'_)=_
    rw [original]
    change decodeState r0=committedRoot p 0
    rw [model0,state_roundtrip]
  · change decodeState (out.roots.val[1]'_)=_
    rw [original]
    change decodeState r1=committedRoot p 1
    rw [model1,state_roundtrip]

#print axioms roots
end AspisR1.F3L_PreparedRoots
end
