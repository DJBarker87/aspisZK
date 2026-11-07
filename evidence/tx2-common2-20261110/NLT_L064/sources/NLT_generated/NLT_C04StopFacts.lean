import NLT_C04StopParent
import NLT_NativeFacts
set_option autoImplicit false
noncomputable section
namespace NLT_C04StopFacts
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
theorem member (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length=57607)
 (records : List (Occurrence H d hash)) (cut : NLT_C04Stop.Cut H)
 (stopped : NLT_C04Stop.At H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) records cut)
 (r : Occurrence H d hash) (atRecord : r∈records) :
 let f:=NLT_FrameFromCuts.frame records
 actual r∈(run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none).events := by
 obtain ⟨reply,suffix,events⟩:=NLT_C04StopParent.source_prefix H d pub proof ck hash len records cut stopped
 dsimp only
 rw [events]
 exact List.mem_append_left _ (List.mem_map.mpr ⟨r,atRecord,rfl⟩)
/-- C01's native input scope is discharged even when the later C04 runtime
call never returns. No completed parent invocation is required. -/
theorem resume_scope (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length=57607) (pubLen : pub.val.length≤1880)
 (records : List (Occurrence H d hash)) (cut : NLT_C04Stop.Cut H)
 (stopped : NLT_C04Stop.At H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) records cut)
 (r : Occurrence H d hash) (atRecord : r∈records) : NLT_NativeFacts.ResumeScope r.entered r.input := by
 have entered:=member H d pub proof ck hash len records cut stopped r atRecord
 let f:=NLT_FrameFromCuts.frame records
 rcases r with ⟨e,input,detail⟩
 cases e <;> try exact True.intro
 case resume c pr pu reply =>
  have arguments:=NLB_C01Domain.source f.resume f.pending (NLP_NativeMerkle.action H)
   (NLB_Parent.finish f.finish) d pub proof ck hash _ entered
  rcases arguments with ⟨rfl,rfl,rfl⟩
  exact NLP_ResumeInstall.scope input _ _ _ len pubLen
set_option pp.proofs false
#print resume_scope
#print axioms member
#print axioms resume_scope
end NLT_C04StopFacts
