import RPu_FJc_GroupTable
set_option autoImplicit false
namespace AspisR1.FJc_S2Rows
/-- D18's S2 digit permutation after separating two low quaternary digits
from the remaining three. This is the arithmetic target for native row_loop. -/
def row (j s : Nat) : Nat :=
  64*(s%4)+256*(s/4)+(j%4)*16+(j/4%4)+4*(j/16)

def activeMask (r : Nat) : Nat :=
  match FIo_Native.aspis_core.r0.opening.COPY_ACTIVE_ROW_MASKS.val[r/16]? with
  | some m=>m.val | none=>0

def inactive (j s : Nat) : Prop := (activeMask (row j s) >>> (row j s%16)) &&& 1=0
instance (j s : Nat) : Decidable (inactive j s) := inferInstanceAs (Decidable ((_ &&& 1)=0))

def selected (j s : Nat) : Prop :=
  (FJc_SubsetModel.mask (FJc_GroupTable.group j) &&& 2^s)≠0
instance (j s : Nat) : Decidable (selected j s) := inferInstanceAs (Decidable (_≠0))

theorem row_bound (j s : Nat) (hj : j<64) (hs : s<16) : row j s<1024 := by
  have h1 := Nat.mod_lt s (by decide : 0<4)
  have h2 := Nat.mod_lt j (by decide : 0<4)
  have h3 := Nat.mod_lt (j/4) (by decide : 0<4)
  unfold row
  omega
#print axioms row_bound
end AspisR1.FJc_S2Rows
