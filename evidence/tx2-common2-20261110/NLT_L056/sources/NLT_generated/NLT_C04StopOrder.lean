import NLT_C04Stop
set_option autoImplicit false
noncomputable section
namespace NLT_C04StopOrder
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation NLT_SiteOrder
/-- Strict order is also proved for a native cut with NO returned C04 reply. -/
theorem ordered {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 {A : Type} (p : Program Event A) (records : List (Occurrence H d hash)) (cut : NLT_C04Stop.Cut H)
 (stopped : NLT_C04Stop.At H d hash p records cut) (n : Nat) (shape : Shape n p) :
 (∀ record∈records,n≤rank (actual record)) ∧
 records.Pairwise (fun left right=>rank (actual left)<rank (actual right)) ∧
 n≤3 ∧ (∀ record∈records,rank (actual record)<3) := by
 induction stopped generalizing n with
 | prim_ok value next records cut tail ih =>
   cases shape with
   | prim _ _ _ shaped => exact ih n (shaped value)
 | call_ok codec seed next record same value decoded records cut tail ih =>
   cases shape with
   | call _ _ _ _ bound shaped =>
     have rest:=ih _ (shaped value)
     have head:=NLT_NativeOrder.rank_call codec seed record same
     refine ⟨?_,?_,?_,?_⟩
     · intro r member
       rcases List.mem_cons.mp member with equal|member
       · subst r;omega
       · have h:=rest.1 r member;omega
     · apply List.Pairwise.cons
       · intro r member;have h:=rest.1 r member;omega
       · exact rest.2.1
     · omega
     · intro r member
       rcases List.mem_cons.mp member with equal|member
       · subst r;omega
       · exact rest.2.2.2 r member
 | stopped codec seed next cut same =>
   cases shape with
   | call _ _ _ _ bound shaped =>
     have rankEq:=congrArg rank same
     rw [NLT_NativeWindows.rank_question] at rankEq
     change rank (codec.encode seed)=3 at rankEq
     exact ⟨by simp,List.Pairwise.nil,by omega,by simp⟩
set_option pp.proofs false
#print ordered
#print axioms ordered
end NLT_C04StopOrder
