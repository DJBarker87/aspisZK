import NLT_NativeSource
set_option autoImplicit false
noncomputable section
namespace NLT_NativeFacts
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
theorem member (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length=57607)
 (result : R Unit) (records : List (Occurrence H d hash))
 (native : Invocation H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) result records)
 (r : Occurrence H d hash) (atRecord : r∈records) :
 let f:=NLT_FrameFromCuts.frame records
 actual r∈(run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none).events := by
 have joined:=NLT_NativeSource.source H d pub proof ck hash len result records native
 rw [←joined.2]
 exact List.mem_map.mpr ⟨r,atRecord,rfl⟩
def ResumeScope : (e : Event) → NLT_NativeWindows.Input e → Prop
 | .resume ck proof pub _,r => NKU_CallerScope.Inputs (NKU.initial ⟨ck,proof,pub,r⟩).frame
 | _,_ => True
/-- Native resume's caller scope comes from the parent's own original inputs,
not from a successful resume observation. The exact local reservation remains
unrestricted, including allocation failure. -/
theorem resume_scope (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length=57607) (pubLen : pub.val.length≤1880)
 (result : R Unit) (records : List (Occurrence H d hash))
 (native : Invocation H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) result records)
 (r : Occurrence H d hash) (atRecord : r∈records) : ResumeScope r.entered r.input := by
 have entered:=member H d pub proof ck hash len result records native r atRecord
 let f:=NLT_FrameFromCuts.frame records
 rcases r with ⟨e,input,detail⟩
 cases e <;> try exact True.intro
 case resume c pr pu reply =>
  have arguments:=NLB_C01Domain.source f.resume f.pending (NLP_NativeMerkle.action H)
   (NLB_Parent.finish f.finish) d pub proof ck hash _ entered
  rcases arguments with ⟨rfl,rfl,rfl⟩
  exact NLP_ResumeInstall.scope input ck proof pub len pubLen
set_option pp.proofs false
#print member
#print resume_scope
#print axioms member
#print axioms resume_scope
end NLT_NativeFacts
