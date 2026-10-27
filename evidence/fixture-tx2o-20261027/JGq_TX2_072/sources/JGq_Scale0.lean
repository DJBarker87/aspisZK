import JGq_Powers0
import JGo_TX2_WeightData
import FJg_ScalarFold
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
  unfold FJg_ScalarFold.body FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
  rw [JGo_TX2_Range.next 0#usize 4#usize 1#usize (by decide) (by decide),bind_tc_ok]
  change (do
    let (v,c) ← FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (JGq_Powers0.a4,row) (v0,0#usize)
    ok (.cont ({start:=1#usize,«end»:=4#usize},c,v)))=_
  rw [call0,bind_tc_ok]
#print axioms step0
theorem call1 : FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (JGq_Powers0.a4,row) (v1,1#usize)=ok (v2,(JGq_Powers0.a4,row)) := by with_unfolding_all rfl
#print axioms call1
theorem step1 : FJg_ScalarFold.body ({start:=1#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v1)=
    ok (.cont ({start:=2#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v2)) := by
  unfold FJg_ScalarFold.body FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
  rw [JGo_TX2_Range.next 1#usize 4#usize 2#usize (by decide) (by decide),bind_tc_ok]
  change (do
    let (v,c) ← FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (JGq_Powers0.a4,row) (v1,1#usize)
    ok (.cont ({start:=2#usize,«end»:=4#usize},c,v)))=_
  rw [call1,bind_tc_ok]
#print axioms step1
theorem call2 : FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (JGq_Powers0.a4,row) (v2,2#usize)=ok (v3,(JGq_Powers0.a4,row)) := by with_unfolding_all rfl
#print axioms call2
theorem step2 : FJg_ScalarFold.body ({start:=2#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v2)=
    ok (.cont ({start:=3#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v3)) := by
  unfold FJg_ScalarFold.body FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
  rw [JGo_TX2_Range.next 2#usize 4#usize 3#usize (by decide) (by decide),bind_tc_ok]
  change (do
    let (v,c) ← FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (JGq_Powers0.a4,row) (v2,2#usize)
    ok (.cont ({start:=3#usize,«end»:=4#usize},c,v)))=_
  rw [call2,bind_tc_ok]
#print axioms step2
theorem call3 : FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (JGq_Powers0.a4,row) (v3,3#usize)=ok (v4,(JGq_Powers0.a4,row)) := by with_unfolding_all rfl
#print axioms call3
theorem step3 : FJg_ScalarFold.body ({start:=3#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v3)=
    ok (.cont ({start:=4#usize,«end»:=4#usize},(JGq_Powers0.a4,row),v4)) := by
  unfold FJg_ScalarFold.body FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
  rw [JGo_TX2_Range.next 3#usize 4#usize 4#usize (by decide) (by decide),bind_tc_ok]
  change (do
    let (v,c) ← FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      (JGq_Powers0.a4,row) (v3,3#usize)
    ok (.cont ({start:=4#usize,«end»:=4#usize},c,v)))=_
  rw [call3,bind_tc_ok]
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
  unfold FIo_Native.weights.Weights.scalar_factor
    FIo_Native.core.iter.traits.iterator.Iterator.fold.default FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop
  change (do
    let sum ← loop FJg_ScalarFold.body (states 0)
    FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 sum FIo_Native.weights.QUARTER)=_
  rw [folded,bind_tc_ok,scaled]
#print axioms source
end AspisR1.JGq_Scale0
end
