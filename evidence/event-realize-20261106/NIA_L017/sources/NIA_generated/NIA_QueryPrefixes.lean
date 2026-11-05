import NIA_ConstructorTrace
import NHS_QueryFailures
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIA_QueryPrefixes
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1PublicPreparation
open NFW_PreparedControl NHL_PreparedScalars NIA_ScalarEffects NIA_ConstructorOpening NIA_ConstructorTrace

variable (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (old : Scratch)
 (packet : NHL_OpeningPacket.Packet (NGQ_Effects.dictionary hashv) sem v ())
 (observed : NGP_L181.Observation NGQ_Effects.Reply)
 (cuts : NHK_Invocation.Cuts hashv packet.opening.transcript packet.opening.row v.final_message observed)

include packet
theorem opening_trace : ∃ earlier,
 NGQ_Cuts.Trace hashv (seedCode sem v) (.ok packet.opening) earlier := by
 obtain ⟨earlier,t⟩ := NIA_ScalarEffects.complete hashv (seedCode sem v)
 have same := (seed_evaluate hashv sem v).trans (NHL_OpeningPacket.result _ _ _ _ packet)
 exact ⟨earlier,by rw [same] at t; exact t⟩

include cuts
/-- Consume the actual NHK invocation's occurrence log, not an invented log
selected from a desired query result. Normalization transport is already in NHS. -/
theorem query_trace : NGQ_Cuts.Trace hashv
 (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries packet.opening.transcript packet.opening.row v.final_message)
 observed.result observed.attempted := by
 have native := (NHS_QueryPacket.source hashv sem v () packet observed cuts).1
 obtain ⟨events,t⟩ := NIA_ScalarEffects.complete hashv
   (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries packet.opening.transcript packet.opening.row v.final_message)
 have same := (NGQ_Cuts.run t []).symm.trans native.symm
 have values := congrArg Prod.fst same
 have logs := congrArg Prod.snd same
 simp only [List.nil_append] at values logs
 rw [←values,←logs]
 exact t

theorem error (e : verifier.Error) (after : transcript.Transcript Unit)
 (returned : observed.result=.ok (.Err e,after)) :
 ∃ earlier, NGQ_Cuts.Trace hashv (code sem v old) (.ok (.Err e,old)) (earlier++observed.attempted) := by
 obtain ⟨earlier,head⟩ := opening_trace hashv sem v packet
 have child := query_trace hashv sem v packet observed cuts
 rw [returned] at child
 have tail : NGQ_Cuts.Trace hashv (queryCode sem v old packet.opening) (.ok (.Err e,old)) observed.attempted := by
   let next : NGQ_Effects.Reply → Code Out := fun (r,after) =>
     .step (core.result.Result.Insts.CoreOpsTry.branch r) fun cf =>
     match cf with
     | .Continue queries => rhoCode sem v packet.opening queries after
     | .Break residual =>
       .step (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
         verifier.Prepared (core.convert.FromSame verifier.Error) residual) fun returned =>
       .done (returned,old)
   have stopped : NGQ_Cuts.Trace hashv (next (.Err e,after)) (.ok (.Err e,old)) [] := by
     apply NGQ_Cuts.Trace.stepOk _ _ _ rfl
     apply NGQ_Cuts.Trace.stepOk _ _ _ rfl
     exact .done _
   simpa only [List.append_nil,next] using
     NHK_TraceBind.append child next (.ok (.Err e,old)) [] stopped
 exact ⟨earlier,NHK_TraceBind.append head _ _ _ tail⟩

theorem fail (e : Error) (returned : observed.result=.fail e) :
 ∃ earlier, NGQ_Cuts.Trace hashv (code sem v old) (.fail e) (earlier++observed.attempted) := by
 obtain ⟨earlier,head⟩ := opening_trace hashv sem v packet
 have child := query_trace hashv sem v packet observed cuts
 rw [returned] at child
 have tail : NGQ_Cuts.Trace hashv (queryCode sem v old packet.opening) (.fail e) observed.attempted := by
   unfold queryCode
   simpa only [List.append_nil] using NHK_TraceBind.append child _ _ [] ⟨rfl,rfl⟩
 exact ⟨earlier,NHK_TraceBind.append head _ _ _ tail⟩

theorem div (returned : observed.result=.div) :
 ∃ earlier, NGQ_Cuts.Trace hashv (code sem v old) .div (earlier++observed.attempted) := by
 obtain ⟨earlier,head⟩ := opening_trace hashv sem v packet
 have child := query_trace hashv sem v packet observed cuts
 rw [returned] at child
 have tail : NGQ_Cuts.Trace hashv (queryCode sem v old packet.opening) .div observed.attempted := by
   unfold queryCode
   simpa only [List.append_nil] using NHK_TraceBind.append child _ _ [] ⟨rfl,rfl⟩
 exact ⟨earlier,NHK_TraceBind.append head _ _ _ tail⟩

#print axioms opening_trace
#print axioms query_trace
#print axioms error
#print axioms fail
#print axioms div
end AspisR1.NIA_QueryPrefixes
