import RPz8_F3V_Decoded
import RPz7_PAln_SelectedAccepted
import RPz7_RawSourceGlobalOracleInitial
/-! PIN2 W7 (2026-11-11): restated on the PIN2 public transcript, as
RPz7_PAln_Public.  `D`, `t0`, `init` and the `public_bytes` and
`SemanticTranscript.new` conjuncts are retargeted to the PIN2 carrier through
W3c's field copy `PreparationBinding.toPIN2`; the `parsePublic` conjunct is
textually unchanged; the serializer success is W3b's
`PIN2_NHG_PublicCarrier.same_execution`. -/
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.F3V_PublicModel
open AspisR1PublicPreparation
open AspisR1CurrentCaller
open MultiproofConeCanonical

theorem from_decode {F C : Type} (c : DrvC_Installation.Configuration F C)
    (physical : Slice U8) (statement : AdapterRw.Cuts.Statement) (semantic : Port1_Driver.Semantic)
    (decodedCall : (DrvC_Installation.sdk c).op47 physical=ok (.Ok statement))
    (selection : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      statement=ok semantic)
    (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 Unit) (root : Array U8 32#usize)
    (t0 : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript Unit)
    (init : AspisR1PublicPreparationPIN2.r1_semantic.public_transcript D
      (PreparationBinding.toPIN2
        (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic semantic))) () root=ok (.Ok t0)) :
    ∃ encoded decoded,
      AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (PreparationBinding.toPIN2
          (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic semantic)))=ok (.Ok encoded) ∧
      SemanticPublicWire.parsePublic (bytesOf encoded.val)=some decoded ∧
      AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new D () (alloc.vec.Vec.deref encoded) root=ok (.Ok t0) := by
  have decoded := AspisS6CurrentCodecInstallation.decode_success physical statement decodedCall
  have selected := AspisS6CurrentFirstInstallation.selected_public statement
  rw [selection,bind_tc_ok] at selected
  have pubEq := congrArg FirstComposition.toRetainedPublic (Result.ok.inj selected)
  rw [FirstComposition.retained_current_roundtrip] at pubEq
  rw [pubEq] at init ⊢
  obtain ⟨encoded,serialized,_,new⟩ := PIN2_NHG_PublicCarrier.same_execution D _ () root t0 init
  obtain ⟨old,wire,serializedOld,wireSource,parsed,newOld⟩ :=
    PreparationBinding.decoder_helper_parsePublic D physical
      (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 statement)
      () root t0 decoded init
  have oldCall : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (AspisR1TerminalDecoder.PublicBinding.toSerializer
        (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 statement))=ok (.Ok encoded) := by
    rw [← PreparationBinding.projection_eq]
    exact serialized
  have eq : old=encoded := core.result.Result.Ok.inj (Result.ok.inj (serializedOld.symm.trans oldCall))
  subst old
  exact ⟨encoded,_,serialized,parsed,new⟩

#print axioms from_decode
end AspisR1.F3V_PublicModel
end
