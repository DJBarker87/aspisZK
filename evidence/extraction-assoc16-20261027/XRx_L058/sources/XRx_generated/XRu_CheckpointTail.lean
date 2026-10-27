import XRr_CheckpointAttempts
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XRu_CheckpointTail
def wides (p : verifier.Prepared) (a : verifier.Accumulator) :=
 [p.gamma,p.kappa,p.alpha.val[0]?.getD p.gamma,p.alpha.val[1]?.getD p.gamma,p.claim,a.rhs].mapM
 aspis_core.field.wide_exact.WideExact.to_le_bytes
/-- The third attempted digest continues THIS model checkpoint after its
actual proof/public/serializer cuts; no native opaque-leaf claim is made. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (p : verifier.Prepared) (a : verifier.Accumulator) (proof physical : Slice U8) (hash : H)
 (proofHash publicHash : Array U8 32#usize) (wide : List (Array U8 32#usize)) (payload : Slice U8)
 (hp : XRn_Join_digest D hash [proof]=ok proofHash)
 (hu : XRn_Join_digest D hash [physical]=ok publicHash)
 (hw : wides p a=ok wide)
 (hs : XRn_Join_asSlice (XRr_CheckpointLayout.bytes p a proofHash publicHash wide)=ok payload) :
 verifier.checkpoint D p a proof physical hash=
 (do
  let checksum ← XRn_Join_digest D hash [XRr_CheckpointAttempts.label,payload]
  let out := XRr_CheckpointLayout.bytes p a proofHash publicHash wide++checksum.val
  if out.length=(if p.variant matches .S1 then 4840 else 1768)
  then XRn_Join_asSlice out else fail .panic) := by
 unfold verifier.checkpoint
 rw [hp,bind_tc_ok,hu,bind_tc_ok]
 change (do
  let wide ← wides p a
  let payload ← XRn_Join_asSlice (XRr_CheckpointLayout.bytes p a proofHash publicHash wide)
  let checksum ← XRn_Join_digest D hash [XRr_CheckpointAttempts.label,payload]
  let out := XRr_CheckpointLayout.bytes p a proofHash publicHash wide++checksum.val
  if out.length=(if p.variant matches .S1 then 4840 else 1768)
  then XRn_Join_asSlice out else fail .panic)=_
 rw [hw,bind_tc_ok,hs]
 rfl
#print axioms source
end XRu_CheckpointTail
