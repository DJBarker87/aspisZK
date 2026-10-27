import XRn_Join_CheckpointModel
import XRk_ResultTools
open Aeneas Aeneas.Std Result
open XRn_Join_Release XRn_Join_FieldExternal XRk_ResultTools
namespace XRr_CheckpointLayout
/-- Exact physical-byte expression of the supplied checkpoint MODEL. Native
serialization, allocation and attempted-call trace correspondence remain open. -/
def bytes (p : verifier.Prepared) (a : verifier.Accumulator)
    (proofHash publicHash : Array U8 32#usize) (wideBytes : List (Array U8 32#usize)) : List U8 :=
  let variant : U8 := match p.variant with | .S1 => 1#u8 | .S2 => 2#u8 | .D => 3#u8
  let next : U8 := UScalar.ofNat (a.next.val%256) (by change _ ≤ 255; omega)
  let initialWide := (wideBytes.take 4).flatMap Subtype.val
  let finalWide := (wideBytes.drop 4).flatMap Subtype.val

  [82#u8,49#u8,80#u8,50#u8,67#u8,75#u8,80#u8,50#u8] ++
    [variant,next,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8] ++
    proofHash.val ++ publicHash.val ++ p.state.val ++
    p.roots.val.flatMap Subtype.val ++ initialWide ++ XRn_Join_qBytes p.rho ++
    p.queries.val.flatMap XRn_Join_wordBytes ++ p.semantic_alpha.val.flatMap XRn_Join_qBytes ++
    p.z.val.flatMap (fun z => XRn_Join_qBytes z.x ++ XRn_Join_qBytes z.y) ++
    finalWide ++ XRn_Join_qBytes a.power ++ a.weights.val.flatMap XRn_Join_qBytes
def label : Slice U8 := ⟨[85#u8,78#u8,80#u8,82#u8,79#u8,86#u8,69#u8,68#u8,58#u8,82#u8,49#u8,58#u8,99#u8,104#u8,101#u8,99#u8,107#u8,112#u8,111#u8,105#u8,110#u8,116#u8],by scalar_tac⟩

theorem slice (xs : List U8) (out : Slice U8) (run : XRn_Join_asSlice xs=ok out) : out.val=xs := by
  unfold XRn_Join_asSlice at run
  split at run
  · cases Result.ok.inj run; rfl
  · cases run

#print axioms slice
end XRr_CheckpointLayout
