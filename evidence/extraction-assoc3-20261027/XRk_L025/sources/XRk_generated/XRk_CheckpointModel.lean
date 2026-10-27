import XRk_CircleModel
open Aeneas Aeneas.Std Result ControlFlow Error
open XRk_Release XRk_FieldExternal
/- XRi_reference_checkpoint: serializer and three ordered digest applications.
   Capacity/allocator/ownership, source and emitted-carrier P6 OPEN. -/
def XRk_asSlice (xs : List U8) : Result (Slice U8) :=
  if h : xs.length ≤ Usize.max then ok ⟨xs,h⟩ else fail .panic
def XRk_digest {H : Type} (d : aspis_core.digest.Digest32 H) (h : H) (xs : List (Slice U8)) : Result (Array U8 32#usize) :=
  if bound : xs.length ≤ Usize.max then d.digest h ⟨xs,bound⟩ else fail .panic

def verifier.checkpoint {H : Type} (d : aspis_core.digest.Digest32 H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof public : Slice U8) (hash : H) :
    Result (alloc.vec.Vec U8) := do
  let proofHash ← XRk_digest d hash [proof]
  let publicHash ← XRk_digest d hash [public]
  let variant : U8 := match p.variant with | .S1 => 1#u8 | .S2 => 2#u8 | .D => 3#u8
  let next : U8 := UScalar.ofNat (a.next.val%256) (by change _ ≤ 255; omega)
  let wideBytes ← [p.gamma,p.kappa,p.alpha.val[0]?.getD p.gamma,p.alpha.val[1]?.getD p.gamma,p.claim,a.rhs].mapM
    aspis_core.field.wide_exact.WideExact.to_le_bytes
  let initialWide := (wideBytes.take 4).flatMap Subtype.val
  let finalWide := (wideBytes.drop 4).flatMap Subtype.val
  let bs :=
    [82#u8,49#u8,80#u8,50#u8,67#u8,75#u8,80#u8,50#u8] ++
    [variant,next,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8] ++
    proofHash.val ++ publicHash.val ++ p.state.val ++
    p.roots.val.flatMap Subtype.val ++ initialWide ++ XRk_qBytes p.rho ++
    p.queries.val.flatMap XRk_wordBytes ++ p.semantic_alpha.val.flatMap XRk_qBytes ++
    p.z.val.flatMap (fun z => XRk_qBytes z.x ++ XRk_qBytes z.y) ++
    finalWide ++ XRk_qBytes a.power ++ a.weights.val.flatMap XRk_qBytes
  let payload ← XRk_asSlice bs
  let label : Slice U8 := ⟨[85#u8,78#u8,80#u8,82#u8,79#u8,86#u8,69#u8,68#u8,58#u8,82#u8,49#u8,58#u8,99#u8,104#u8,101#u8,99#u8,107#u8,112#u8,111#u8,105#u8,110#u8,116#u8],by decide⟩
  let checksum ← XRk_digest d hash [label,payload]
  let out := bs ++ checksum.val
  let size := if p.variant matches .S1 then 4840 else 1768
  if out.length = size then XRk_asSlice out else fail .panic

/- Library models use explicit ordered messages; source/P6 and allocation OPEN. -/
def aspis_core.r0.heap.filled {T : Type} (_ : core.marker.Copy T) (n : Usize) (v : T) :
    Result (core.result.Result (alloc.vec.Vec T) aspis_core.r0.Error) :=
  dite (n.val ≤ Usize.max) (fun h => ok (.Ok ⟨List.replicate n.val v,by simpa only [List.length_replicate] using h⟩)) (fun _ => ok (.Err .Allocation))
def aspis_core.r0.merkle.parent_with_digest {H : Type} (d : aspis_core.digest.Digest32 H)
    (h : H) (children : Array (Array U8 32#usize) 8#usize) : Result (Array U8 32#usize) :=
  XRk_digest d h (⟨[24#u8],by decide⟩ :: children.val.map Array.to_slice)
def aspis_core.state_only_private_merkle.private_leaf_hash_with_digest {H : Type}
    (d : aspis_core.digest.Digest32 H) (h : H) (tag : U8) (v : Slice U8) (salt : Array U8 32#usize) :
    Result (Array U8 32#usize) :=
  XRk_digest d h [⟨[16#u8,tag],by decide⟩,v,salt.to_slice]
