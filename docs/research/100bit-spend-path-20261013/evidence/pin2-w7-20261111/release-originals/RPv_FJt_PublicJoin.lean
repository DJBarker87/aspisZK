import RPv_FJq_SourceLiteralPublic
import RPv_FJa_PublicOnPreparation
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJt_PublicJoin
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIz_ConcretePack (embed)

theorem value {H : Type} (D : aspis_core.Digest32 H)
    (pub : FIq_Carriers.Public) (s : AspisR1TerminalDecoder.PublicBinding.Statement)
    (physical : Slice U8)
    (decoded : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
      physical=ok (.Ok s))
    (same : pub=PreparationBinding.preparationPublic s)
    (hash : H) (root : Array U8 32#usize) (t0 : r1_wire.SemanticTranscript H)
    (init : r1_semantic.public_transcript D pub hash root=ok (.Ok t0))
    (encoded : alloc.vec.Vec U8)
    (serialized : pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub=ok (.Ok encoded))
    (literal : LiteralTranscript.Public) (literalPub : R0P.Public SemanticPublicWire.M31)
    (bytesSame : literal.pubBytes=SourceDigestAddresses.rawBytes encoded.deref)
    (parsed : SemanticPublicWire.parsePublic literal.pubBytes=some literalPub) :
    FJa_PublicBounds.Bounds (FJa_PublicCopy.native pub) ∧
    SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic (FJa_PublicCopy.native pub))=
      SpendDataMap.mapPublic ExactBaseProjection.embed literalPub := by
  subst pub
  have bounds:=FJa_PublicBounds.from_raw s (ActualPublicFieldBounds.public_transcript_fields_canonical D s hash root t0 init)
  obtain ⟨bytes,wire,old,mapped,parse,new⟩:=PreparationBinding.decoder_helper_parsePublic D physical s hash root t0 decoded init
  have oldCall : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (AspisR1TerminalDecoder.PublicBinding.toSerializer s)=ok (.Ok encoded) := by
    rw [←PreparationBinding.projection_eq,SerializerWhole.serializer_eq,serialized]
    rfl
  have eq:=core.result.Result.Ok.inj (Result.ok.inj (old.symm.trans oldCall))
  subst bytes
  exact ⟨bounds,FJq_SourceLiteralPublic.value s encoded wire mapped parse literal.pubBytes literalPub bytesSame parsed⟩
#print axioms value
end AspisR1.FJt_PublicJoin
end
