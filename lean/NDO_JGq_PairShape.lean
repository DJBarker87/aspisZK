import NDO_JGq_Powers0
import NDO_JGq_Powers1
import NDO_JGq_PowersK
import NDO_JGo_TX2_FinishPrefix
import NDO_JGo_TX2_PairGuard
import RPv_FJm_Filled
import RPu_FJf_CommonIndices
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_PairShape
open Aeneas Aeneas.Std Result ControlFlow
abbrev E := FIo_Install.NE
abbrev Q := FIo_Install.NQ
def f := JFw_Frames.window 8007 2048
def alpha := FIo_Install.toSlice JGo_TX2_FinishPrefix.alphas
def w := FIo_Install.toWeights JGo_TX2_WeightData.value
def kappa := FIo_Install.toE JFo_Prepared.value.kappa
def scratch : alloc.vec.Vec Q := ⟨List.replicate 64 FIo_Native.aspis_core.field.QM31.ZERO,by simp;scalar_tac⟩

theorem length : Slice.len f=2048#usize := by
  apply UScalar.eq_of_val_eq
  rw [Slice.len_val]
  exact JFw_Frames.window_length 8007 2048 (by decide)
#print axioms length
theorem divided : (2048#usize / 32#usize : Result Usize)=ok 64#usize := by rfl
#print axioms divided
theorem folds : Slice.len alpha=2#usize := by rfl
#print axioms folds

abbrev S := core.ops.range.Range Usize × Usize
def states : Nat → S
  | 0 => ({start:=0#usize,«end»:=2#usize},1024#usize)
  | 1 => ({start:=1#usize,«end»:=2#usize},256#usize)
  | _ => ({start:=2#usize,«end»:=2#usize},64#usize)
theorem expected0 : FIo_Native.weights.Weights.pair_loop0.body
    {start:=0#usize,«end»:=2#usize} 1024#usize=ok (.cont ({start:=1#usize,«end»:=2#usize},256#usize)) := by
  have shift : Usize.wrapping_shr 1024#usize 2#u32=256#usize :=
    UScalar.eq_of_val_eq (by rw [FJf_CommonIndices.high];rfl)
  unfold FIo_Native.weights.Weights.pair_loop0.body
  rw [JGo_TX2_Range.next 0#usize 2#usize 1#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,shift]
#print axioms expected0
theorem expected1 : FIo_Native.weights.Weights.pair_loop0.body
    {start:=1#usize,«end»:=2#usize} 256#usize=ok (.cont ({start:=2#usize,«end»:=2#usize},64#usize)) := by
  have shift : Usize.wrapping_shr 256#usize 2#u32=64#usize :=
    UScalar.eq_of_val_eq (by rw [FJf_CommonIndices.high];rfl)
  unfold FIo_Native.weights.Weights.pair_loop0.body
  rw [JGo_TX2_Range.next 1#usize 2#usize 2#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,shift]
#print axioms expected1
theorem expected : FIo_Native.weights.Weights.pair_loop0 {start:=0#usize,«end»:=2#usize} 1024#usize=ok 64#usize := by
  unfold FIo_Native.weights.Weights.pair_loop0
  apply JGo_TX2_LoopChain.source
    (fun s : S=>FIo_Native.weights.Weights.pair_loop0.body s.1 s.2) states 2 64#usize
  · intro i hi
    interval_cases i
    · exact expected0
    · exact expected1
  · unfold FIo_Native.weights.Weights.pair_loop0.body
    with_unfolding_all rfl
#print axioms expected

theorem read0 : Slice.index_usize alpha 0#usize=ok JGq_Powers0.x := by rfl
#print axioms read0
theorem read1 : Slice.index_usize alpha 1#usize=ok JGq_Powers1.x := by rfl
#print axioms read1
theorem filled : @FIo_Native.aspis_core.r0.heap.filled (FIo_Install.allocation (.Ok ())) Q
    FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy 64#usize FIo_Native.aspis_core.field.QM31.ZERO=ok (.Ok scratch) :=
  FJm_Filled.contents (.Ok ()) 64#usize
#print axioms filled
end AspisR1.JGq_PairShape
end
