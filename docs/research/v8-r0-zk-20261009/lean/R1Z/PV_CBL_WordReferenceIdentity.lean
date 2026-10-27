import R1Z.PV_CBL_WordReference
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_WordReferenceIdentity
open PV_CBL_WordReference
set_option autoImplicit false

theorem q (x : Q) : copyQ x=x := rfl

theorem word (w : Word) : copyWord w=w := by
  have hq : copyQ=id := by funext x; rfl
  cases w with
  | Base v =>
    apply congrArg ProverRwFull.host_commitment.Word.Base
    apply Subtype.ext
    simp only [copyWord,List.map_id]
  | Secure v =>
    apply congrArg ProverRwFull.host_commitment.Word.Secure
    apply Subtype.ext
    simp only [copyWord,hq,List.map_id]

theorem item (r : Item) : copyItem r=r := by
  cases r with
  | Ok w => exact congrArg core.result.Result.Ok (word w)
  | Err e => rfl

theorem items (v : alloc.vec.Vec Item) : copyItems v=v := by
  apply Subtype.ext
  have h : copyItem=id := by funext r; exact item r
  simp only [copyItems,h,List.map_id]
#print axioms q
#print axioms word
#print axioms item
#print axioms items
end R1Z.PV_CBL_WordReferenceIdentity
