import RPu_FJc_FieldValue
import RPu_FJc_ArrayUpdateValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_InactiveCoefficientsModel
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE wide)
/-- Source table coordinates, read as data, not as a source execution oracle. -/
def group (j : Nat) : Nat :=
  match FIo_Native.weights.S2_INACTIVE_GROUPS.val[j]? with | some g => g.val | none => 0

def field (f : Slice U8) (j : Nat) : AspisWideTower.WideExact :=
  (FoldedLeafCodec.decodeWide (OraclePortCompactDraft.slice
    (MultiproofConeCanonical.bytesOf f.val) (32*j) 32)).getD 0

def sumPrefix (f : Slice U8) (g : Nat) : Nat → AspisWideTower.WideExact
  | 0 => 0
  | n+1 => sumPrefix f g n + if group n=g then field f n else 0

theorem group_read (j : Usize) (g : U8)
    (run : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS j=ok g) : group j.val=g.val := by
  simp only [group,FJc_ReadSlot.slot _ j g run]

theorem field_read (f : Slice U8) (j : Usize) (out : NE) (hj : j.val<64)
    (run : FIo_Native.weights.field f j=ok out) :
    field f j.val=AspisR1CurrentWide.Proof.decodeWide (wide out) := by
  simp only [field,FJc_FieldValue.value f j out hj run,Option.getD_some]
#print axioms group_read
#print axioms field_read
end AspisR1.FJc_InactiveCoefficientsModel
end
