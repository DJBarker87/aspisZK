import NLT_NativeInvocation
set_option autoImplicit false
noncomputable section
namespace NLT_NativeOrder
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NLT_NativeInvocation NLT_SiteOrder
theorem rank_call {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 {B : Type} (codec : Codec Event B) (seed : Result B) (record : Occurrence H d hash)
 (same : NLT_NativeWindows.question record.entered=NLT_NativeWindows.question (codec.encode seed)) :
 rank (actual record)=rank (codec.encode seed) := by
 have question:=congrArg rank same
 rw [NLT_NativeWindows.rank_question,NLT_NativeWindows.rank_question] at question
 exact (NLT_NativeWindows.rank_window H d hash record.entered record.input).trans question
/-- Every possible interpreted native trace follows the same strictly ordered
sites, including errors and nonreturning prefixes. Thus two occurrences cannot
silently select different reservations for the same allocation site. -/
theorem ordered {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 {A : Type} (p : Program Event A) (result : Result A) (records : List (Occurrence H d hash))
 (native : Invocation H d hash p result records) (n : Nat) (shape : Shape n p) :
 (∀ record∈records,n≤rank (actual record)) ∧
 records.Pairwise (fun left right=>rank (actual left)<rank (actual right)) := by
 induction native generalizing n with
 | ret value => exact ⟨by simp,List.Pairwise.nil⟩
 | prim_ok value next result records tail ih =>
   cases shape with
   | prim _ _ _ shaped => exact ih n (shaped value)
 | prim_fail error next => exact ⟨by simp,List.Pairwise.nil⟩
 | prim_div next => exact ⟨by simp,List.Pairwise.nil⟩
 | call_ok codec seed next record same value decoded result records tail ih =>
   cases shape with
   | call _ _ _ _ bound shaped =>
     have rest:=ih _ (shaped value)
     have head:=rank_call codec seed record same
     constructor
     · intro r member
       rcases List.mem_cons.mp member with equal|member
       · subst r;omega
       · have h:=rest.1 r member;omega
     · apply List.Pairwise.cons
       · intro r member
         have h:=rest.1 r member
         omega
       · exact rest.2
 | call_fail codec seed next record same error decoded =>
   cases shape with
   | call _ _ _ _ bound shaped =>
     have head:=rank_call codec seed record same
     exact ⟨by intro r member;have equal:=List.mem_singleton.mp member;subst r;omega,by simp⟩
 | call_div codec seed next record same decoded =>
   cases shape with
   | call _ _ _ _ bound shaped =>
     have head:=rank_call codec seed record same
     exact ⟨by intro r member;have equal:=List.mem_singleton.mp member;subst r;omega,by simp⟩
set_option pp.proofs false
#print rank_call
#print ordered
#print axioms rank_call
#print axioms ordered
end NLT_NativeOrder
