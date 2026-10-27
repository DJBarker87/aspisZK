import LPb_CheckpointSequence
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
open LPb_CheckpointLayout LPb_CheckpointSequence
namespace LPb_CheckpointAttempts

theorem first_failure {H : Type} (D : aspis_core.digest.Digest32 H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) (hash : H)
    (e : Error) (h : XRk_digest D hash [proof] = fail e) :
    logged D p a proof pub hash = ([[proof]],fail e) := by
  simp only [logged,LPb_Logged.attempt,h,LPb_Logged.bind]

theorem second_failure {H : Type} (D : aspis_core.digest.Digest32 H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) (hash : H)
    (ph : Array U8 32#usize) (e : Error)
    (h1 : XRk_digest D hash [proof] = ok ph)
    (h2 : XRk_digest D hash [pub] = fail e) :
    logged D p a proof pub hash = ([[proof],[pub]],fail e) := by
  simp only [logged,LPb_Logged.attempt,h1,h2,LPb_Logged.bind,List.singleton_append,List.nil_append]

theorem successful_stages {H : Type} (D : aspis_core.digest.Digest32 H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) (hash : H)
    (ph uh checksum : Array U8 32#usize) (ws : List (Array U8 32#usize))
    (payload : Slice U8) (out : alloc.vec.Vec U8)
    (h1 : XRk_digest D hash [proof] = ok ph)
    (h2 : XRk_digest D hash [pub] = ok uh)
    (hw : wideStages p a = ok ws)
    (hp : XRk_asSlice (bytes p a ph uh ws) = ok payload)
    (h3 : XRk_digest D hash [label,payload] = ok checksum)
    (hf : lastStage p (bytes p a ph uh ws) checksum = ok out) :
    logged D p a proof pub hash = ([[proof],[pub],[label,payload]],ok out) := by
  simp only [logged,LPb_Logged.attempt,LPb_Logged.lift,h1,h2,hw,hp,h3,hf,LPb_Logged.bind,
    List.singleton_append,List.nil_append,List.append_nil]
#print axioms first_failure
#print axioms second_failure
#print axioms successful_stages
end LPb_CheckpointAttempts
