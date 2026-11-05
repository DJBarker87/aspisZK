import NIA_ScalarEffects
import NHS_PreparedPacket
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIA_ConstructorOpening
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1PublicPreparation
open NFW_PreparedControl NHL_PreparedScalars NIA_ScalarEffects

/-- Seed/new has one read, even on unsuccessful digest return. -/
def newCode (state : Array U8 32#usize) (variant : transport.Variant) : Code (transcript.Transcript Unit) :=
 .step (transport.Variant.tag variant) fun tag =>
 .read (Array.to_slice (Array.make 3#usize [Array.to_slice NGT_NBA_Transcript.domain,
   Array.to_slice (Array.make 1#usize [tag]),Array.to_slice state])) fun reply =>
 .done ⟨reply,()⟩

def foldCode (v : verifier.View) (gamma kappa alpha0 : PE)
 (before : transcript.Transcript Unit) : Code (Opening Unit) :=
 .step (transport.Variant.folds v.variant) fun folds =>
 if folds=2#usize then
   .step (NHL_PreparedOpening.foldPayload v) fun payload =>
   CheckpointBytes5Effect.bind (scalarCode actual.sampling before 30#u8 payload false) fun (alpha1,after) =>
   .done ⟨gamma,kappa,Array.make 2#usize [alpha0,alpha1],after,31#u8⟩
 else .done ⟨gamma,kappa,Array.make 2#usize [alpha0,aspis_core.field.WideExact.ZERO],before,30#u8⟩

def alphaCode (v : verifier.View) (gamma kappa : PE) (before : transcript.Transcript Unit) : Code (Opening Unit) :=
 CheckpointBytes5Effect.bind (scalarCode actual.sampling before 29#u8 v.round0 false)
   fun (alpha0,after) => foldCode v gamma kappa alpha0 after

def kappaCode (v : verifier.View) (gamma : PE) (before : transcript.Transcript Unit) : Code (Opening Unit) :=
 .step (actual.sampling.toBytes v.inactive) fun bytes =>
 CheckpointBytes5Effect.bind (scalarCode actual.sampling before 28#u8 (Array.to_slice bytes) false)
   fun (kappa,after) => alphaCode v gamma kappa after

def gammaCode (v : verifier.View) (before : transcript.Transcript Unit) : Code (Opening Unit) :=
 CheckpointBytes5Effect.bind (scalarCode actual.sampling before 27#u8 v.y1 true)
   fun (gamma,after) => kappaCode v gamma after

def seedCode (sem : r1_semantic.Verified Unit) (v : verifier.View) : Code (Opening Unit) :=
 .step (r1_wire.SemanticTranscript.impl.state NGQ_Effects.dummy sem.transcript) fun state =>
 CheckpointBytes5Effect.bind (newCode state v.variant) (gammaCode v)

theorem new_evaluate (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (state : Array U8 32#usize) (variant : transport.Variant) :
 evaluate hashv (newCode state variant)=transcript.Transcript.new (NGQ_Effects.dictionary hashv) () state variant := by
 simp only [newCode,evaluate,transcript.Transcript.new,NGQ_Effects.dictionary,
   NGT_NBA_Transcript.domain,lift,bind_tc_ok]

theorem fold_evaluate (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (v : verifier.View) (gamma kappa alpha0 : PE) (before : transcript.Transcript Unit) :
 evaluate hashv (foldCode v gamma kappa alpha0 before)=
 NGN_Opening.foldCut actual (NGQ_Effects.dictionary hashv) v gamma kappa alpha0 before := by
 unfold foldCode NGN_Opening.foldCut
 simp only [evaluate]
 congr 1
 funext folds
 split
 · simp only [evaluate,evaluate_bind,scalar_evaluate,NHL_PreparedOpening.foldPayload,
     bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
   rfl
 · rfl

theorem alpha_evaluate (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (v : verifier.View) (gamma kappa : PE) (before : transcript.Transcript Unit) :
 evaluate hashv (alphaCode v gamma kappa before)=
 NGN_Opening.alphaCut actual (NGQ_Effects.dictionary hashv) v gamma kappa before := by
 simp only [alphaCode,evaluate_bind,scalar_evaluate,fold_evaluate,NGN_Opening.alphaCut,Aeneas.Std.uncurry]
 rfl

theorem kappa_evaluate (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (v : verifier.View) (gamma : PE) (before : transcript.Transcript Unit) :
 evaluate hashv (kappaCode v gamma before)=
 NGN_Opening.kappaCut actual (NGQ_Effects.dictionary hashv) v gamma before := by
 simp only [kappaCode,evaluate,evaluate_bind,scalar_evaluate,alpha_evaluate,NGN_Opening.kappaCut,lift,bind_tc_ok,Aeneas.Std.uncurry]
 rfl

theorem gamma_evaluate (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (v : verifier.View) (before : transcript.Transcript Unit) :
 evaluate hashv (gammaCode v before)=
 NGN_Opening.gammaCut actual (NGQ_Effects.dictionary hashv) v before := by
 simp only [gammaCode,evaluate_bind,scalar_evaluate,kappa_evaluate,NGN_Opening.gammaCut,Aeneas.Std.uncurry]
 rfl

theorem seed_evaluate (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) :
 evaluate hashv (seedCode sem v)=NGN_Opening.seedCut actual (NGQ_Effects.dictionary hashv) sem v () := by
 simp only [seedCode,evaluate,evaluate_bind,new_evaluate,gamma_evaluate,NGN_Opening.seedCut]
 rfl

#print axioms new_evaluate
#print axioms fold_evaluate
#print axioms alpha_evaluate
#print axioms kappa_evaluate
#print axioms gamma_evaluate
#print axioms seed_evaluate
end AspisR1.NIA_ConstructorOpening
