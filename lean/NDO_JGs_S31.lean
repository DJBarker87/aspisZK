import NDO_JGq_Powers1
import NDO_JGo_TX2_WeightData
import RPv_FJg_ScalarFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_S31
open Aeneas Aeneas.Std Result ControlFlow
abbrev E := FIo_Install.NE
def row : Array FIo_Install.NQ 4#usize := FIn_WeightsInstall.mapArray FIo_Install.toQ JGo_TX2_WeightData.f31
def v0 : E := ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
def v1 : E := ⟨⟨⟨1#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
def v2 : E := ⟨⟨⟨518758630#u32,213579353#u32⟩,⟨1296539219#u32,422053672#u32⟩⟩,⟨⟨19311062#u32,1160432026#u32⟩,⟨1386870107#u32,220584102#u32⟩⟩⟩
def v3 : E := ⟨⟨⟨467683752#u32,1740216488#u32⟩,⟨2063837022#u32,2116819116#u32⟩⟩,⟨⟨1615628232#u32,524442115#u32⟩,⟨922043110#u32,1875384847#u32⟩⟩⟩
def v4 : E := ⟨⟨⟨111529754#u32,1664320132#u32⟩,⟨1792856478#u32,1504542176#u32⟩⟩,⟨⟨234182891#u32,397470798#u32⟩,⟨1333738668#u32,1854288476#u32⟩⟩⟩
def value : E := ⟨⟨⟨1101624262#u32,416080033#u32⟩,⟨1521955943#u32,376135544#u32⟩⟩,⟨⟨1669158458#u32,1173109523#u32⟩,⟨333434667#u32,463572119#u32⟩⟩⟩
theorem call0 : FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (JGq_Powers1.a4,row) (v0,0#usize)=ok (v1,(JGq_Powers1.a4,row)) := by with_unfolding_all rfl
#print axioms call0
theorem step0 : FJg_ScalarFold.body ({start:=0#usize,«end»:=4#usize},(JGq_Powers1.a4,row),v0)=
    ok (.cont ({start:=1#usize,«end»:=4#usize},(JGq_Powers1.a4,row),v1)) := by
  change FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
    FJg_ScalarFold.iterator FJg_ScalarFold.operation
    {start:=0#usize,«end»:=4#usize} (JGq_Powers1.a4,row) v0=_
  unfold FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
  dsimp only [FJg_ScalarFold.iterator,core.iter.traits.iterator.IteratorRange,FJg_ScalarFold.operation]
  rw [JGo_TX2_Range.next 0#usize 4#usize 1#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [call0]
  with_unfolding_all rfl
#print axioms step0
theorem call1 : FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (JGq_Powers1.a4,row) (v1,1#usize)=ok (v2,(JGq_Powers1.a4,row)) := by with_unfolding_all rfl
#print axioms call1
theorem step1 : FJg_ScalarFold.body ({start:=1#usize,«end»:=4#usize},(JGq_Powers1.a4,row),v1)=
    ok (.cont ({start:=2#usize,«end»:=4#usize},(JGq_Powers1.a4,row),v2)) := by
  change FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
    FJg_ScalarFold.iterator FJg_ScalarFold.operation
    {start:=1#usize,«end»:=4#usize} (JGq_Powers1.a4,row) v1=_
  unfold FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
  dsimp only [FJg_ScalarFold.iterator,core.iter.traits.iterator.IteratorRange,FJg_ScalarFold.operation]
  rw [JGo_TX2_Range.next 1#usize 4#usize 2#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [call1]
  with_unfolding_all rfl
#print axioms step1
theorem call2 : FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (JGq_Powers1.a4,row) (v2,2#usize)=ok (v3,(JGq_Powers1.a4,row)) := by with_unfolding_all rfl
#print axioms call2
theorem step2 : FJg_ScalarFold.body ({start:=2#usize,«end»:=4#usize},(JGq_Powers1.a4,row),v2)=
    ok (.cont ({start:=3#usize,«end»:=4#usize},(JGq_Powers1.a4,row),v3)) := by
  change FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
    FJg_ScalarFold.iterator FJg_ScalarFold.operation
    {start:=2#usize,«end»:=4#usize} (JGq_Powers1.a4,row) v2=_
  unfold FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
  dsimp only [FJg_ScalarFold.iterator,core.iter.traits.iterator.IteratorRange,FJg_ScalarFold.operation]
  rw [JGo_TX2_Range.next 2#usize 4#usize 3#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [call2]
  with_unfolding_all rfl
#print axioms step2
theorem call3 : FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (JGq_Powers1.a4,row) (v3,3#usize)=ok (v4,(JGq_Powers1.a4,row)) := by with_unfolding_all rfl
#print axioms call3
theorem step3 : FJg_ScalarFold.body ({start:=3#usize,«end»:=4#usize},(JGq_Powers1.a4,row),v3)=
    ok (.cont ({start:=4#usize,«end»:=4#usize},(JGq_Powers1.a4,row),v4)) := by
  change FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
    FJg_ScalarFold.iterator FJg_ScalarFold.operation
    {start:=3#usize,«end»:=4#usize} (JGq_Powers1.a4,row) v3=_
  unfold FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
  dsimp only [FJg_ScalarFold.iterator,core.iter.traits.iterator.IteratorRange,FJg_ScalarFold.operation]
  rw [JGo_TX2_Range.next 3#usize 4#usize 4#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [call3]
  with_unfolding_all rfl
#print axioms step3
def states : Nat → FJg_ScalarFold.State
  | 0 => ({start:=0#usize,«end»:=4#usize},(JGq_Powers1.a4,row),v0)
  | 1 => ({start:=1#usize,«end»:=4#usize},(JGq_Powers1.a4,row),v1)
  | 2 => ({start:=2#usize,«end»:=4#usize},(JGq_Powers1.a4,row),v2)
  | 3 => ({start:=3#usize,«end»:=4#usize},(JGq_Powers1.a4,row),v3)
  | _ => ({start:=4#usize,«end»:=4#usize},(JGq_Powers1.a4,row),v4)
theorem folded : loop FJg_ScalarFold.body (states 0)=ok v4 := by
  apply JGo_TX2_LoopChain.source FJg_ScalarFold.body states 4 v4
  · intro i hi
    interval_cases i
    · exact step0
    · exact step1
    · exact step2
    · exact step3
  · unfold FJg_ScalarFold.body FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
    with_unfolding_all rfl
#print axioms folded
theorem scaled : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 v4 FIo_Native.weights.QUARTER=ok value := by with_unfolding_all rfl
#print axioms scaled
theorem source : FIo_Native.weights.Weights.scalar_factor row JGq_Powers1.a4=ok value := by
  have run : FIo_Native.core.iter.traits.iterator.Iterator.fold.default FJg_ScalarFold.iterator FJg_ScalarFold.operation
      {start:=0#usize,«end»:=4#usize} FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO (JGq_Powers1.a4,row)=ok v4 := by
    unfold FIo_Native.core.iter.traits.iterator.Iterator.fold.default FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop
    have eta : (fun t : FJg_ScalarFold.State=>match t with
        | (r,c,v)=>FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
          FJg_ScalarFold.iterator FJg_ScalarFold.operation r c v)=FJg_ScalarFold.body := by
      funext t
      rcases t with ⟨r,c,v⟩
      rfl
    rw [eta]
    with_unfolding_all exact folded
  unfold FIo_Native.weights.Weights.scalar_factor
  rw [run,bind_tc_ok,scaled]
#print axioms source
end AspisR1.JGs_S31
end
