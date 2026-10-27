import LPb_CheckpointNativeGap
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
open LPb_CheckpointLayout LPb_CheckpointSequence
namespace LPb_CheckpointPrefixes

theorem wide_failure {H : Type} (D : aspis_core.digest.Digest32 H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) (hash : H)
    (ph uh : Array U8 32#usize) (e : Error)
    (h1 : XRk_digest D hash [proof] = ok ph)
    (h2 : XRk_digest D hash [pub] = ok uh)
    (hw : wideStages p a = fail e) :
    logged D p a proof pub hash = ([[proof],[pub]],fail e) := by
  simp only [logged,LPb_Logged.attempt,LPb_Logged.lift,h1,h2,hw,LPb_Logged.bind,
    List.singleton_append,List.nil_append]

theorem payload_failure {H : Type} (D : aspis_core.digest.Digest32 H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) (hash : H)
    (ph uh : Array U8 32#usize) (ws : List (Array U8 32#usize)) (e : Error)
    (h1 : XRk_digest D hash [proof] = ok ph)
    (h2 : XRk_digest D hash [pub] = ok uh)
    (hw : wideStages p a = ok ws)
    (hp : XRk_asSlice (bytes p a ph uh ws) = fail e) :
    logged D p a proof pub hash = ([[proof],[pub]],fail e) := by
  simp only [logged,LPb_Logged.attempt,LPb_Logged.lift,h1,h2,hw,hp,LPb_Logged.bind,
    List.singleton_append,List.nil_append]

theorem checksum_failure {H : Type} (D : aspis_core.digest.Digest32 H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) (hash : H)
    (ph uh : Array U8 32#usize) (ws : List (Array U8 32#usize)) (payload : Slice U8) (e : Error)
    (h1 : XRk_digest D hash [proof] = ok ph)
    (h2 : XRk_digest D hash [pub] = ok uh)
    (hw : wideStages p a = ok ws)
    (hp : XRk_asSlice (bytes p a ph uh ws) = ok payload)
    (h3 : XRk_digest D hash [label,payload] = fail e) :
    logged D p a proof pub hash = ([[proof],[pub],[label,payload]],fail e) := by
  simp only [logged,LPb_Logged.attempt,LPb_Logged.lift,h1,h2,hw,hp,h3,LPb_Logged.bind,
    List.singleton_append,List.nil_append]
#print axioms wide_failure
#print axioms payload_failure
#print axioms checksum_failure
end LPb_CheckpointPrefixes
