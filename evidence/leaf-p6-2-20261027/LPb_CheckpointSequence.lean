import LPb_Logged
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
open LPb_CheckpointLayout
namespace LPb_CheckpointSequence

def wideStages (p : verifier.Prepared) (a : verifier.Accumulator) :=
  [p.gamma,p.kappa,p.alpha.val[0]?.getD p.gamma,p.alpha.val[1]?.getD p.gamma,p.claim,a.rhs].mapM
    aspis_core.field.wide_exact.WideExact.to_le_bytes

def lastStage (p : verifier.Prepared) (bs : List U8) (sum : Array U8 32#usize) :
    Result (alloc.vec.Vec U8) :=
  let out := bs ++ sum.val
  let size := if p.variant matches .S1 then 4840 else 1768
  if out.length = size then XRk_asSlice out else fail .panic

def sequence {H : Type} (D : aspis_core.digest.Digest32 H) (p : verifier.Prepared)
    (a : verifier.Accumulator) (proof pub : Slice U8) (hash : H) : Result (alloc.vec.Vec U8) := do
  let ph ← XRk_digest D hash [proof]
  let uh ← XRk_digest D hash [pub]
  let ws ← wideStages p a
  let bs := bytes p a ph uh ws
  let payload ← XRk_asSlice bs
  let sum ← XRk_digest D hash [label,payload]
  lastStage p bs sum

theorem checkpoint_model_stages {H : Type} (D : aspis_core.digest.Digest32 H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) (hash : H) :
    verifier.checkpoint D p a proof pub hash = sequence D p a proof pub hash := rfl

/-- Record each attempted digest before inspecting its returned Result. -/
def logged {H : Type} (D : aspis_core.digest.Digest32 H) (p : verifier.Prepared)
    (a : verifier.Accumulator) (proof pub : Slice U8) (hash : H) :
    LPb_Logged.Run (alloc.vec.Vec U8) :=
  LPb_Logged.bind (LPb_Logged.attempt D hash [proof]) fun ph =>
  LPb_Logged.bind (LPb_Logged.attempt D hash [pub]) fun uh =>
  LPb_Logged.bind (LPb_Logged.lift (wideStages p a)) fun ws =>
  let bs := bytes p a ph uh ws
  LPb_Logged.bind (LPb_Logged.lift (XRk_asSlice bs)) fun payload =>
  LPb_Logged.bind (LPb_Logged.attempt D hash [label,payload]) fun sum =>
  LPb_Logged.lift (lastStage p bs sum)

theorem erase {H : Type} (D : aspis_core.digest.Digest32 H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8) (hash : H) :
    (logged D p a proof pub hash).2 = verifier.checkpoint D p a proof pub hash := by
  rw [checkpoint_model_stages]
  simp only [logged,LPb_Logged.erase_bind,LPb_Logged.lift,LPb_Logged.attempt,sequence]

#print axioms checkpoint_model_stages
#print axioms erase
end LPb_CheckpointSequence
