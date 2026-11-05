import NIA_ConstructorOpening
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIA_ConstructorTrace
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1PublicPreparation
open NFW_PreparedControl NHL_PreparedScalars NIA_ScalarEffects NIA_ConstructorOpening

def claimCode (sem : r1_semantic.Verified Unit) (v : verifier.View) (g : Scratch)
 (o : Opening Unit) (queries : Array U32 22#usize) (rho : aspis_core.field.QM31)
 (last : transcript.Transcript Unit) : Code Out :=
 liftResult (NGN_Cuts.claimCut actual NGQ_Effects.dummy sem v g o queries rho last)

def powersCode (sem : r1_semantic.Verified Unit) (v : verifier.View)
 (o : Opening Unit) (queries : Array U32 22#usize) (rho : aspis_core.field.QM31)
 (last : transcript.Transcript Unit) : Code Out :=
 .step (actual.powers 29#usize o.gamma) fun g => claimCode sem v g o queries rho last

def rhoCode (sem : r1_semantic.Verified Unit) (v : verifier.View)
 (o : Opening Unit) (queries : Array U32 22#usize) (after : transcript.Transcript Unit) : Code Out :=
 .step (o.row+1#u8) fun row =>
 CheckpointBytes5Effect.bind (scalarKCode actual.sampling after row PreparedScratchReachability.emptyPayload)
   fun (rho,last) => powersCode sem v o queries rho last

def queryCode (sem : r1_semantic.Verified Unit) (v : verifier.View)
 (old : Scratch) (o : Opening Unit) : Code Out :=
 CheckpointBytes5Effect.bind
   (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries o.transcript o.row v.final_message) fun (r,after) =>
 .step (core.result.Result.Insts.CoreOpsTry.branch r) fun cf =>
 match cf with
 | .Continue queries => rhoCode sem v o queries after
 | .Break residual =>
   .step (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     verifier.Prepared (core.convert.FromSame verifier.Error) residual) fun returned =>
   .done (returned,old)

def code (sem : r1_semantic.Verified Unit) (v : verifier.View) (old : Scratch) : Code Out :=
 CheckpointBytes5Effect.bind (seedCode sem v) (queryCode sem v old)

theorem evaluate_run (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 {A : Type} (p : Code A) (before : SdkC_Source.Log) :
 evaluate hashv p=(SdkC_Source.run hashv p before).1 := by
 obtain ⟨events,t⟩ := complete hashv p
 exact (congrArg Prod.fst (NGQ_Cuts.run t before)).symm

/-- The installed prepared-claim body does not use the digest parameter. This
is an equality of actual closed definitions, not a free callback assumption. -/
theorem claim_dictionary (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (g : Scratch)
 (o : Opening Unit) (queries : Array U32 22#usize) (rho : aspis_core.field.QM31)
 (last : transcript.Transcript Unit) :
 NGN_Cuts.claimCut actual NGQ_Effects.dummy sem v g o queries rho last=
 NGN_Cuts.claimCut actual (NGQ_Effects.dictionary hashv) sem v g o queries rho last := rfl

theorem powers_evaluate (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View)
 (o : Opening Unit) (queries : Array U32 22#usize) (rho : aspis_core.field.QM31)
 (last : transcript.Transcript Unit) :
 evaluate hashv (powersCode sem v o queries rho last)=
 NGN_Cuts.powersCut actual (NGQ_Effects.dictionary hashv) sem v o queries rho last := by
 simp only [powersCode,evaluate,claimCode,evaluate_lift,claim_dictionary,NGN_Cuts.powersCut]

theorem rho_evaluate (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View)
 (o : Opening Unit) (queries : Array U32 22#usize) (after : transcript.Transcript Unit) :
 evaluate hashv (rhoCode sem v o queries after)=
 NGN_Cuts.rhoCut actual (NGQ_Effects.dictionary hashv) sem v o queries after := by
 simp only [rhoCode,evaluate,evaluate_bind,scalarK_evaluate,powers_evaluate,NGN_Cuts.rhoCut,
   PreparedScratchReachability.emptyPayload,lift,bind_tc_ok]
 rfl

theorem query_evaluate (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (old : Scratch) (o : Opening Unit) :
 evaluate hashv (queryCode sem v old o)=
 NGN_Cuts.queryCut actual (NGQ_Effects.dictionary hashv) sem v old o := by
 have q := (evaluate_run hashv (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries o.transcript o.row v.final_message) []).trans
   (NGQ_Effects.model_result hashv NGQ_TRANSCRIPT.boundaries o.transcript o.row v.final_message)
 simp only [queryCode,evaluate_bind,q,NGN_Cuts.queryCut,NHL_QueryInterface.dictionary]
 congr 1
 funext pair
 rcases pair with ⟨r,after⟩
 simp only [evaluate]
 congr 1
 funext cf
 cases cf <;> simp only [rho_evaluate,evaluate]

theorem source_result (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (old : Scratch) :
 evaluate hashv (code sem v old)=NGN_Emitted.prepared actual (NGQ_Effects.dictionary hashv) sem v () old := by
 rw [NGN_EmittedEq.staged]
 simp only [code,evaluate_bind,seed_evaluate,query_evaluate]

/-- Complete MODEL trace, uniformly over success, scalar S1-S4/S6 stops, S5
Rust Error/fail/div, claim Error/fail/div and every pure constructor failure.
There is no successful-constructor premise or assumed complete trace. Native
logging/parent-installation is explicitly not concluded by this theorem. -/
theorem source (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (old : Scratch) :
 ∃ events, NGQ_Cuts.Trace hashv (code sem v old)
   (NGN_Emitted.prepared actual (NGQ_Effects.dictionary hashv) sem v () old) events := by
 obtain ⟨events,t⟩ := complete hashv (code sem v old)
 exact ⟨events,by rw [source_result] at t; exact t⟩

theorem frame (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (old : Scratch) :
 ∃ events, ∀ before, SdkC_Source.run hashv (code sem v old) before=
   (NGN_Emitted.prepared actual (NGQ_Effects.dictionary hashv) sem v () old,before++events) := by
 obtain ⟨events,t⟩ := source hashv sem v old
 exact ⟨events,NGQ_Cuts.run t⟩

#print axioms evaluate_run
#print axioms claim_dictionary
#print axioms powers_evaluate
#print axioms rho_evaluate
#print axioms query_evaluate
#print axioms source_result
#print axioms source
#print axioms frame
end AspisR1.NIA_ConstructorTrace
