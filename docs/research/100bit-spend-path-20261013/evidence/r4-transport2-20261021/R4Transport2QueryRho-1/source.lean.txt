import R4Transport2QueryAbsorb
import R4Transport2CirclePrefix
import R4TransportRhoSource

/-! Row32 consumes the query-selected state. The exact remaining source scan
relation appears as hscan, rather than being hidden in a prefix-state premise. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.R4Transport2QueryRho
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisR1 AspisV8R15.ExactTowerBase
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open TranscriptStep SourceDigestAddresses

def emptyPayload : Slice U8 := Array.to_slice (Std.Array.empty U8)

def rhoMessage : LiteralTranscript.Message :=
  .payload (R4Transport2OpeningChain.message emptyPayload (by change 4 ≤ 3717; decide))

/-- The successful reference scan fixes row32's preceding state and its empty
frame. This is a composition theorem, retaining the real source/driver join. -/
theorem rho_after_selected_query {Hash : Type} (B : PreparedModel.Boundaries)
    (D : aspis_core.Digest32 Hash) (self after : transcript.Transcript Hash)
    (q : aspis_core.field.QM31)
    (hcall : PreparedModel.scalar_k B D self 32#u8 emptyPayload = ok (q,after))
    (P : LiteralTranscript.Prefix) (m31 : LiteralTranscript.Message)
    (blocks states : Nat → State) (out : List Nat)
    (hscan : R4Transport2ScanComposition.pairsRun R0C.V3.Q22.q0
      (R4Transport2QueryPrefix.pairs blocks states) (states 0) = (.ok out,decodeState self.state))
    (H : Bytes → State)
    (hquery : (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
      (LiteralTranscript.samp 31 P m31).toProgram).2 =
      UnifiedSampler.liftQuery (R4Transport2ScanComposition.pairsRun R0C.V3.Q22.q0
        (R4Transport2QueryPrefix.pairs blocks states) (states 0)))
    (hdigest : ∀ hash parts result, D.digest hash parts = ok result →
      decodeState result = H (flatten parts)) :
    (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
      (LiteralTranscript.samp 32 (R4Transport2CirclePrefix.extendModel H 31 P m31)
        rhoMessage).toProgram).2 =
      (.ordinary (algebraMap QM31Exact AspisWideTower.WideExact (R4TransportRhoSource.decodeQM q)),
        decodeState after.state) := by
  have hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (R4Transport2CirclePrefix.extendModel H 31 P m31)) =
      decodeState self.state := by
    rw [R4Transport2CirclePrefix.extendModel, LiteralTranscript.erasePrefix_ext,
      UnifiedSampler.stateOf_ext, hquery, hscan]
    rfl
  exact R4TransportRhoSource.rho_call_transport B D self after emptyPayload q hcall
    _ rhoMessage (R4Transport2OpeningChain.message emptyPayload _) rfl hstate
    (UScalar.cast .U32 (Slice.len emptyPayload)) rfl rfl H hdigest

#print axioms rho_after_selected_query
end AspisR1PublicPreparation.R4Transport2QueryRho
end
