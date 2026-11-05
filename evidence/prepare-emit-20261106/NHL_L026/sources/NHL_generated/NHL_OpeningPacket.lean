import NHL_PreparedOpening
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_OpeningPacket
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NFW_PreparedControl
open NHL_PreparedScalars

/-- The two concrete source branches; no whole-output equality field. -/
inductive Fold {H : Type} (D : aspis_core.Digest32 H) (v : verifier.View)
 (gamma kappa alpha0 : aspis_core.field.WideExact) (before : transcript.Transcript H) : Opening H → Prop where
 | single (folds : transport.Variant.folds v.variant=ok 1#usize) :
   Fold D v gamma kappa alpha0 before
     ⟨gamma,kappa,Array.make 2#usize [alpha0,aspis_core.field.WideExact.ZERO],before,30#u8⟩
 | double (folds : transport.Variant.folds v.variant=ok 2#usize)
   (payload : Slice U8) (produced : NHL_PreparedOpening.foldPayload v=ok payload)
   (b : NGT_NBL_BlockTrace.Block D before 30#u8 payload)
   (alpha1 : aspis_core.field.WideExact) (reduction : NGT_Reduction.Scalar b.value false alpha1) :
   Fold D v gamma kappa alpha0 before
     ⟨gamma,kappa,Array.make 2#usize [alpha0,alpha1],{before with state:=b.final},31#u8⟩

theorem fold_result {H : Type} {D : aspis_core.Digest32 H} {v : verifier.View}
 {gamma kappa alpha0 : aspis_core.field.WideExact} {before : transcript.Transcript H} {o : Opening H}
 (packet : Fold D v gamma kappa alpha0 before o) :
 NGN_Opening.foldCut actual D v gamma kappa alpha0 before=ok o := by
 cases packet with
 | single folds => exact NHL_PreparedOpening.single D v gamma kappa alpha0 before folds
 | double folds payload produced b alpha1 reduction =>
   exact NHL_PreparedOpening.double D v gamma kappa alpha0 alpha1 before folds payload produced b reduction

theorem fold_fields {H : Type} {D : aspis_core.Digest32 H} {v : verifier.View}
 {gamma kappa alpha0 : aspis_core.field.WideExact} {before : transcript.Transcript H} {o : Opening H}
 (packet : Fold D v gamma kappa alpha0 before o) :
 o.gamma=gamma ∧ o.kappa=kappa ∧ (o.row=30#u8 ∨ o.row=31#u8) := by
 cases packet with
 | single _ => exact ⟨rfl,rfl,Or.inl rfl⟩
 | double _ _ _ _ _ _ => exact ⟨rfl,rfl,Or.inr rfl⟩

/-- Explicit primitive packet domain: seed/new digest calls, serializer and
three SAME-input NGT block/reduction traces, then the concrete fold branch.
No scalar, claim, queries or constructor success is a field. -/
structure Packet {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
 (v : verifier.View) (hash : H) where
 state : Array U8 32#usize
 start : transcript.Transcript H
 seed : r1_wire.SemanticTranscript.impl.state D sem.transcript=ok state
 newStart : transcript.Transcript.new D hash state v.variant=ok start
 gammaBlock : NGT_NBL_BlockTrace.Block D start 27#u8 v.y1
 gamma : aspis_core.field.WideExact
 gammaReduction : NGT_Reduction.Scalar gammaBlock.value true gamma
 bytes : Array U8 32#usize
 serialize : actual.sampling.toBytes v.inactive=ok bytes
 kappaBlock : NGT_NBL_BlockTrace.Block D {start with state:=gammaBlock.final} 28#u8 (Array.to_slice bytes)
 kappa : aspis_core.field.WideExact
 kappaReduction : NGT_Reduction.Scalar kappaBlock.value false kappa
 alphaBlock : NGT_NBL_BlockTrace.Block D {start with state:=kappaBlock.final} 29#u8 v.round0
 alpha0 : aspis_core.field.WideExact
 alphaReduction : NGT_Reduction.Scalar alphaBlock.value false alpha0
 opening : Opening H
 fold : Fold D v gamma kappa alpha0 {start with state:=alphaBlock.final} opening

theorem result {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
 (v : verifier.View) (hash : H) (packet : Packet D sem v hash) :
 NGN_Opening.seedCut actual D sem v hash=ok packet.opening := by
 rw [NHL_PreparedOpening.prefix_result D sem v hash packet.state packet.start packet.seed packet.newStart
   packet.gammaBlock packet.gamma packet.gammaReduction packet.bytes packet.serialize packet.kappaBlock
   packet.kappa packet.kappaReduction packet.alphaBlock packet.alpha0 packet.alphaReduction]
 exact fold_result packet.fold

theorem gamma_canonical {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
 (v : verifier.View) (hash : H) (packet : Packet D sem v hash) :
 NFN_LPi_FieldValues.canonE (NFW_SampledDomains.toNative packet.opening.gamma) := by
 rw [(fold_fields packet.fold).1]
 exact NGN_ScalarDomains.gamma actual.sampling D packet.start _ v.y1 packet.gamma
   (NGT_CallerInterface.scalar actual.sampling D packet.start 27#u8 v.y1 true packet.gammaBlock packet.gamma packet.gammaReduction)

theorem kappa_canonical {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
 (v : verifier.View) (hash : H) (packet : Packet D sem v hash) :
 NFN_LPi_FieldValues.canonE (NFW_SampledDomains.toNative packet.opening.kappa) := by
 rw [(fold_fields packet.fold).2.1]
 apply NFW_SampledDomains.gamma_canonical
 apply AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic_success_canonical packet.kappaBlock.value packet.kappa
 exact NGT_Reduction.scalar packet.kappaReduction
def nextRow {H : Type} (o : Opening H) : U8 := if o.row=30#u8 then 31#u8 else 32#u8

theorem increment {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
 (v : verifier.View) (hash : H) (packet : Packet D sem v hash) :
 (packet.opening.row+1#u8 : Result U8)=ok (nextRow packet.opening) := by
 rcases (fold_fields packet.fold).2.2 with first|second
 · rw [nextRow,first]
   rfl
 · rw [nextRow,second]
   rfl
#print axioms increment
#print axioms fold_result
#print axioms fold_fields
#print axioms result
#print axioms gamma_canonical
#print axioms kappa_canonical
end AspisR1.NHL_OpeningPacket
