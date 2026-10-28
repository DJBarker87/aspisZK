import PV_L2C_BlockRange
import R0Z.WriterRefineValueModel
set_option autoImplicit false
namespace PV_L2C_ValueRange
open Aeneas Aeneas.Std Result R0Z.WriterRefine PV_L2C_BlockRange

theorem outer (vals : Nat → Nat) (blk : Nat → Nat) (start k : Nat)
    (hv : ∀ j, j < 3 → vals j < 2147483647) (hb : blk k < 2147483647) :
    OuterVal vals start blk k < 2147483647 := by
  unfold OuterVal
  split_ifs with hit hbit hvalue
  · have := Nat.mod_lt (vals (jOf (k/16)) / 2^tOf (2*jOf (k/16)) k) (by omega : 0 < 2)
    omega
  · exact hv _ hit.1
  · exact hb
  · exact hb
#print axioms outer

theorem final (vals : Nat → Nat) (hv : ∀ j, j < 3 → vals j < 2^30) (k : Nat) :
    FinalVal vals k < 2147483647 := by
  have h0 := hv 0 (by omega)
  have h1 := hv 1 (by omega)
  have h2 := hv 2 (by omega)
  unfold FinalVal
  split_ifs
  all_goals first | omega | exact outer vals (fun _ => 0) 0 k (by intro j hj;have := hv j hj;omega) (by omega)
#print axioms final

theorem block (values : Array U32 3#usize) (hv : ∀ j, j < 3 → (values.val[j]!).val < 2^30)
    (out : Array U32 256#usize) (hout : R0WriterCopies.write_value_block values = ok out) :
    Canonical out := by
  obtain ⟨expected,he,hcells⟩ := value_block values hv
  have same : out = expected := Result.ok.inj (hout.symm.trans he)
  intro k hk
  rw [same,hcells]
  exact final _ hv k
#print axioms block
end PV_L2C_ValueRange
