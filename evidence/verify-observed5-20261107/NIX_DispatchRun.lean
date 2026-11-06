import NIX_ProducerInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIX_DispatchRun
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)

/-- Full execution of the returning block continuation. The sole premise is
its SAME-block circle callee equation, supplied below without caller success. -/
theorem returned {H : Type} (B : FinishModel.Boundaries) (row : FinishModel.CircleRow)
 (self : r1_wire.SemanticTranscript H) (block : Array U8 32#usize)
 (point : aspis_core.circle.SecureCirclePoint) (callee : B.circle block row=ok point) :
 run (NIX_ValidatedCut.after B row self (.Ok block))=([],ok (.Ok point,self)) := by
 simp only [NIX_ValidatedCut.after,core.result.Result.Insts.CoreOpsTry.branch,
  NGX_CodeTrace.lift_bind,callee,NGX_CodeTrace.pure_run]

theorem rejected {H : Type} (B : FinishModel.Boundaries) (row : FinishModel.CircleRow)
 (self : r1_wire.SemanticTranscript H) (error : r1_wire.Error) :
 run (NIX_ValidatedCut.after B row self (.Err error))=([],ok (.Err error,self)) := rfl

/-- The installed sampler packet is total and tied to the SAME block and row;
its return value is derived from the retained sampler/circle laws. -/
theorem circle_packet (B : FinishModel.Boundaries) (block : Array U8 32#usize)
 (row : FinishModel.CircleRow) :
 ∃ point,(F3M_CircleSource.install B).circle block row=ok point := by
 obtain ⟨q,mapped,_,_,_,run⟩:=NIX_SamplerLaw.adopted block row
 exact ⟨_,run⟩

/-- SAME arbitrary transcript state, framed slice and row; the block code and
its complete fail/div/error outcomes are retained by bind_run. -/
theorem first {H : Type} (B : FinishModel.Boundaries) (D : aspis_core.Digest32 H)
 (self : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord) :
 run (NIX_ValidatedCut.dispatch B D self record 25#u8)=
 NGX_RunBind.appendResult (run (S1SemanticCode.sampleBlock D self 25#u8 record.framed)).1
  (run (S1SemanticCode.sampleBlock D self 25#u8 record.framed)).2
  (fun pair=>NIX_ValidatedCut.after B .First pair.2 pair.1) := by
 change run (S1SemanticCode.sampleBlock D self 25#u8 record.framed >>=
  fun pair=>NIX_ValidatedCut.after B .First pair.2 pair.1)=_
 exact NGX_RunBind.bind_run _ _

theorem second {H : Type} (B : FinishModel.Boundaries) (D : aspis_core.Digest32 H)
 (self : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord) :
 run (NIX_ValidatedCut.dispatch B D self record 26#u8)=
 NGX_RunBind.appendResult (run (S1SemanticCode.sampleBlock D self 26#u8 record.framed)).1
  (run (S1SemanticCode.sampleBlock D self 26#u8 record.framed)).2
  (fun pair=>NIX_ValidatedCut.after B .Second pair.2 pair.1) := by
 change run (S1SemanticCode.sampleBlock D self 26#u8 record.framed >>=
  fun pair=>NIX_ValidatedCut.after B .Second pair.2 pair.1)=_
 exact NGX_RunBind.bind_run _ _

/-- Abort prefixes of the child never execute the circle continuation. -/
theorem abort_prefix {A : Type} {T : Type} (log : PreparedHashCode.Log)
 (next other : A→Code T) :
 (∀ error,NGX_RunBind.appendResult log (.fail error) next=NGX_RunBind.appendResult log (.fail error) other) ∧
 NGX_RunBind.appendResult log .div next=NGX_RunBind.appendResult log .div other := ⟨fun _=>rfl,rfl⟩

#print axioms returned
#print axioms rejected
#print axioms circle_packet
#print axioms first
#print axioms second
#print axioms abort_prefix
end AspisR1.NIX_DispatchRun
end
