import XRk_CheckpointModel
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
namespace LPb_CheckpointLayout
def bytes (p : verifier.Prepared) (a : verifier.Accumulator)
    (proofHash publicHash : Array U8 32#usize) (wideBytes : List (Array U8 32#usize)) : List U8 :=
  let variant : U8 := match p.variant with | .S1 => 1#u8 | .S2 => 2#u8 | .D => 3#u8
  let next : U8 := UScalar.ofNat (a.next.val%256) (by change _ ≤ 255; omega)
  let initialWide := (wideBytes.take 4).flatMap Subtype.val
  let finalWide := (wideBytes.drop 4).flatMap Subtype.val

  [82#u8,49#u8,80#u8,50#u8,67#u8,75#u8,80#u8,50#u8] ++
    [variant,next,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8] ++
    proofHash.val ++ publicHash.val ++ p.state.val ++
    p.roots.val.flatMap Subtype.val ++ initialWide ++ XRk_qBytes p.rho ++
    p.queries.val.flatMap XRk_wordBytes ++ p.semantic_alpha.val.flatMap XRk_qBytes ++
    p.z.val.flatMap (fun z => XRk_qBytes z.x ++ XRk_qBytes z.y) ++
    finalWide ++ XRk_qBytes a.power ++ a.weights.val.flatMap XRk_qBytes
def label : Slice U8 := ⟨[85#u8,78#u8,80#u8,82#u8,79#u8,86#u8,69#u8,68#u8,58#u8,82#u8,49#u8,58#u8,99#u8,104#u8,101#u8,99#u8,107#u8,112#u8,111#u8,105#u8,110#u8,116#u8],by scalar_tac⟩

/-- Header, digests, six wide serializers and the remaining scalar stages.
No native/refinement credit is inferred from this layout definition. -/
def payloadStages (p : verifier.Prepared) (a : verifier.Accumulator)
    (proofHash publicHash : Array U8 32#usize) : Result (Slice U8) := do
  let wideBytes ← [p.gamma,p.kappa,p.alpha.val[0]?.getD p.gamma,p.alpha.val[1]?.getD p.gamma,p.claim,a.rhs].mapM
    aspis_core.field.wide_exact.WideExact.to_le_bytes
  XRk_asSlice (bytes p a proofHash publicHash wideBytes)
def finalize (p : verifier.Prepared) (payload : Slice U8)
    (checksum : Array U8 32#usize) : Result (alloc.vec.Vec U8) :=
  let out := payload.val ++ checksum.val
  let size := if p.variant matches .S1 then 4840 else 1768
  if out.length = size then XRk_asSlice out else fail .panic

theorem slice_value (xs : List U8) (out : Slice U8) (run : XRk_asSlice xs = ok out) :
    out.val = xs := by
  unfold XRk_asSlice at run
  split at run
  · cases Result.ok.inj run; rfl
  · cases run
#print axioms slice_value
end LPb_CheckpointLayout
