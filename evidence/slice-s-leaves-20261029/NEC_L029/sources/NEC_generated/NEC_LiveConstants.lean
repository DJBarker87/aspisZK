import AspisR1TerminalDecoder.Funs
import AdapterRwScalar
set_option autoImplicit false
namespace NEC_LiveConstants
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

def binding : Array U8 32#usize := Array.make 32#usize
 [65#u8,83#u8,80#u8,80#u8,65#u8,73#u8,82#u8,49#u8,
  1#u8,20#u8,21#u8,7#u8,1#u8,1#u8,1#u8,1#u8,
  0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,
  0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]

theorem binding_value : pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING=ok binding := by
 have a21 : 20#usize+1#usize=ok 21#usize :=
  AspisR1.AdapterRw.Scalar.add_eq _ _ _ (by scalar_tac)
 have c20 : UScalar.cast .U8 20#usize=20#u8 := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq]
  scalar_tac
 have c21 : UScalar.cast .U8 21#usize=21#u8 := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq]
  scalar_tac
 have c7 : UScalar.cast .U8 7#usize=7#u8 := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq]
  scalar_tac
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_NOTE_DEPTH
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH pool_v1.format.POOL_V1_TREE_DEPTH
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_SECOND_SENTINEL_LANE
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION
 rw [c20,a21]
 simp only [lift,bind_tc_ok]
 rw [c21,c7]
 rfl

theorem magic : pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val=
 [65#u8,83#u8,80#u8,76#u8,73#u8,86#u8,69#u8,49#u8] := by
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC
 rfl

theorem version : pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION=1#u8 := by
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION
 rfl

theorem live_width : pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES=800#usize := by
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
 rfl

theorem late_width : pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES=ok 1520#usize := by
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES
 unfold pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
 unfold pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
 unfold pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
 have a832 : 32#usize+800#usize=ok 832#usize := AspisR1.AdapterRw.Scalar.add_eq _ _ _ (by scalar_tac)
 have a688 : 8#usize+680#usize=ok 688#usize := AspisR1.AdapterRw.Scalar.add_eq _ _ _ (by scalar_tac)
 rw [a832,a688]
 simp only [bind_tc_ok]
 exact AspisR1.AdapterRw.Scalar.add_eq _ _ _ (by scalar_tac)

theorem after_width : pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES=ok 688#usize := by
 unfold pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
 unfold pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
 exact AspisR1.AdapterRw.Scalar.add_eq _ _ _ (by scalar_tac)

#print axioms binding_value
#print axioms magic
#print axioms version
#print axioms live_width
#print axioms late_width
#print axioms after_width
end NEC_LiveConstants
