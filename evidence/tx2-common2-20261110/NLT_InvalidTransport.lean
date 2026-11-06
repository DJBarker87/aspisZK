import NLT_Invalid
import NLT_NativeOrder
import NLT_ReseedTransport
import NLT_EraseCompatible
set_option autoImplicit false
noncomputable section
namespace NLT_InvalidTransport
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation NLT_SiteOrder
theorem ordered {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 {A : Type} (p : Program Event A) (records : List (Occurrence H d hash))
 (bad : NLT_NativeInvocation.Invalid H d hash p records) (n : Nat) (shape : Shape n p) :
 (∀ record∈records,n≤rank (actual record)) ∧
 records.Pairwise (fun left right=>rank (actual left)<rank (actual right)) := by
 induction bad generalizing n with
 | prim_ok value next records tail ih =>
   cases shape with
   | prim _ _ _ shaped => exact ih n (shaped value)
 | call_ok codec seed next record same value decoded records tail ih =>
   cases shape with
   | call _ _ _ _ bound shaped =>
     have rest:=ih _ (shaped value)
     have head:=NLT_NativeOrder.rank_call codec seed record same
     constructor
     · intro r member
       rcases List.mem_cons.mp member with equal|member
       · subst r;omega
       · have h:=rest.1 r member;omega
     · apply List.Pairwise.cons
       · intro r member;have h:=rest.1 r member;omega
       · exact rest.2
 | mismatch codec seed next record same decoded =>
   cases shape with
   | call _ _ _ _ bound shaped =>
     have head:=NLT_NativeOrder.rank_call codec seed record same
     exact ⟨by intro r member;have equal:=List.mem_singleton.mp member;subst r;omega,by simp⟩
theorem reseed {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 {A : Type} (left right : Program Event A) (same : NLT_Reseed.Same left right)
 (records : List (Occurrence H d hash)) (bad : NLT_NativeInvocation.Invalid H d hash left records) :
 NLT_NativeInvocation.Invalid H d hash right records := by
 induction same generalizing records with
 | ret value => cases bad
 | prim reply left right tail ih =>
   cases bad with
   | prim_ok value _ _ after => exact .prim_ok value right records (ih value _ after)
 | call codec old fresh left right questions tail ih =>
   cases bad with
   | call_ok _ _ _ record entered value decoded rest after =>
     exact .call_ok codec fresh right record (entered.trans questions) value decoded rest (ih value _ after)
   | mismatch _ _ _ record entered decoded =>
     exact .mismatch codec fresh right record (entered.trans questions) decoded
theorem erase {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 {A : Type} (f : NLT_Interpreted.Uninstalled) (p : Program Event A) (records : List (Occurrence H d hash))
 (bad : NLT_NativeInvocation.Invalid H d hash p records)
 (compatible : ∀ r∈records,NLT_NativeWindows.Compatible f r.entered r.input) :
 NLT_Continuation.Invalid (NLT_EraseCompatible.Local f H d hash) p (records.map actual) := by
 induction bad with
 | prim_ok value next records tail ih => exact .prim_ok value next _ (ih compatible)
 | call_ok codec seed next record same value decoded records tail ih =>
   exact NLT_Continuation.Invalid.call_ok codec seed next (actual record)
    ⟨record.entered,record.input,same,compatible record (List.mem_cons_self),rfl⟩ value decoded _
    (ih (fun r member=>compatible r (List.mem_cons_of_mem _ member)))
 | mismatch codec seed next record same decoded =>
   exact .mismatch codec seed next (actual record)
    ⟨record.entered,record.input,same,compatible record (List.mem_singleton_self _),rfl⟩ decoded
set_option pp.proofs false
#print ordered
#print reseed
#print erase
#print axioms ordered
#print axioms reseed
#print axioms erase
end NLT_InvalidTransport
