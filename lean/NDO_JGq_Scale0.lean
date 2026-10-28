import NDO_JGq_Powers0
import NDO_JGo_TX2_WeightData
import RPv_FJg_ScalarFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Scale0
open Aeneas Aeneas.Std Result ControlFlow
abbrev E := FIo_Install.NE
def row : Array FIo_Install.NQ 4#usize := FIn_WeightsInstall.mapArray FIo_Install.toQ JGo_TX2_WeightData.f00
def v0 : E := ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
def v1 : E := ⟨⟨⟨688964259#u32,983935735#u32⟩,⟨1481049653#u32,158732270#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
def v2 : E := ⟨⟨⟨1568540689#u32,536438801#u32⟩,⟨149428006#u32,939758512#u32⟩⟩,⟨⟨1457551078#u32,202023720#u32⟩,⟨562479362#u32,1974062880#u32⟩⟩⟩
def v3 : E := ⟨⟨⟨82050295#u32,1695715304#u32⟩,⟨2056698809#u32,337884405#u32⟩⟩,⟨⟨2117944202#u32,399949132#u32⟩,⟨1351933409#u32,1604237095#u32⟩⟩⟩
def v4 : E := ⟨⟨⟨1417984503#u32,810109760#u32⟩,⟨702315137#u32,310002824#u32⟩⟩,⟨⟨801101492#u32,894682265#u32⟩,⟨267426633#u32,820391910#u32⟩⟩⟩
def value : E := ⟨⟨⟨1965108861#u32,202527440#u32⟩,⟨712449696#u32,77500706#u32⟩⟩,⟨⟨200275373#u32,760541478#u32⟩,⟨603727570#u32,1278839801#u32⟩⟩⟩
theorem call0 : FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (JGq_Powers0.a4,row) (v0,0#usize)=ok (v1,(JGq_Powers0.a4,row)) := by with_unfolding_all rfl
#print axioms call0
theorem step0 : FJg_ScalarFold.body ({start:=0#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v0)=
    ok (.cont ({start:=1#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v1)) := by
  change FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
    FJg_ScalarFold.iterator FJg_ScalarFold.operation
    {start:=0#usize,«end»:=4#usize} (JGq_Powers0.a4,row) v0=_
  unfold FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
  dsimp only [FJg_ScalarFold.iterator,core.iter.traits.iterator.IteratorRange,FJg_ScalarFold.operation]
  rw [JGo_TX2_Range.next 0#usize 4#usize 1#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [call0]
  with_unfolding_all rfl
#print axioms step0
theorem call1 : FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (JGq_Powers0.a4,row) (v1,1#usize)=ok (v2,(JGq_Powers0.a4,row)) := by with_unfolding_all rfl
#print axioms call1
theorem step1 : FJg_ScalarFold.body ({start:=1#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v1)=
    ok (.cont ({start:=2#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v2)) := by
  change FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
    FJg_ScalarFold.iterator FJg_ScalarFold.operation
    {start:=1#usize,«end»:=4#usize} (JGq_Powers0.a4,row) v1=_
  unfold FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
  dsimp only [FJg_ScalarFold.iterator,core.iter.traits.iterator.IteratorRange,FJg_ScalarFold.operation]
  rw [JGo_TX2_Range.next 1#usize 4#usize 2#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [call1]
  with_unfolding_all rfl
#print axioms step1
theorem call2 : FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (JGq_Powers0.a4,row) (v2,2#usize)=ok (v3,(JGq_Powers0.a4,row)) := by with_unfolding_all rfl
#print axioms call2
theorem step2 : FJg_ScalarFold.body ({start:=2#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v2)=
    ok (.cont ({start:=3#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v3)) := by
  change FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
    FJg_ScalarFold.iterator FJg_ScalarFold.operation
    {start:=2#usize,«end»:=4#usize} (JGq_Powers0.a4,row) v2=_
  unfold FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
  dsimp only [FJg_ScalarFold.iterator,core.iter.traits.iterator.IteratorRange,FJg_ScalarFold.operation]
  rw [JGo_TX2_Range.next 2#usize 4#usize 3#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [call2]
  with_unfolding_all rfl
#print axioms step2
theorem call3 : FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (JGq_Powers0.a4,row) (v3,3#usize)=ok (v4,(JGq_Powers0.a4,row)) := by with_unfolding_all rfl
#print axioms call3
theorem step3 : FJg_ScalarFold.body ({start:=3#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v3)=
    ok (.cont ({start:=4#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v4)) := by
  change FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
    FJg_ScalarFold.iterator FJg_ScalarFold.operation
    {start:=3#usize,«end»:=4#usize} (JGq_Powers0.a4,row) v3=_
  unfold FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
  dsimp only [FJg_ScalarFold.iterator,core.iter.traits.iterator.IteratorRange,FJg_ScalarFold.operation]
  rw [JGo_TX2_Range.next 3#usize 4#usize 4#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [call3]
  with_unfolding_all rfl
#print axioms step3
def states : Nat → FJg_ScalarFold.State
  | 0 => ({start:=0#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v0)
  | 1 => ({start:=1#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v1)
  | 2 => ({start:=2#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v2)
  | 3 => ({start:=3#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v3)
  | _ => ({start:=4#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v4)
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
theorem source : FIo_Native.weights.Weights.scalar_factor row JGq_Powers0.a4=ok value := by
  have run : FIo_Native.core.iter.traits.iterator.Iterator.fold.default FJg_ScalarFold.iterator FJg_ScalarFold.operation
      {start:=0#usize,«end»:=4#usize} FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO (JGq_Powers0.a4,row)=ok v4 := by
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
end AspisR1.JGq_Scale0
end
