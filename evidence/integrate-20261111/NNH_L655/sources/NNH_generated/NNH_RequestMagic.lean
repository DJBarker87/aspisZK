import NNH_ByteListInjective
import NNH_Stage2Guards
import NNH_Stage2SourceConfiguration
import NNH_SliceEq
set_option autoImplicit false
noncomputable section
namespace NNH_RequestMagic
open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier

abbrev magic := aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC

theorem get (data : Slice U8) (length : 4≤data.val.length)
 (same : (bytes data).take 4=RSL.REQUEST_MAGIC) :
 core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice U8) data ⟨4#usize⟩=.ok (some magic.to_slice) := by
 have raw : data.val.take 4=magic.val := by
  apply NNH_ByteListInjective.value
  simpa only [bytes,List.map_take,magic,
   aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC,
   RSL.REQUEST_MAGIC] using same
 change (if (4#usize).val≤data.length then Result.ok (some _) else Result.ok none)=_
 rw [if_pos (by simpa only [Slice.length] using length)]
 congr 2
 apply Subtype.ext
 simpa only [List.slice,List.drop_zero] using raw

#print axioms get
end NNH_RequestMagic
