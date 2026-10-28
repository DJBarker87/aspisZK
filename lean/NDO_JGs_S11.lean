import NDO_JGq_Powers1
import NDO_JGo_TX2_WeightData
import RPv_FJg_ScalarFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_S11
open Aeneas Aeneas.Std Result ControlFlow
abbrev E := FIo_Install.NE
def row : Array FIo_Install.NQ 4#usize := FIn_WeightsInstall.mapArray FIo_Install.toQ JGo_TX2_WeightData.f11
def v0 : E := ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
def v1 : E := ⟨⟨⟨69405317#u32,192704168#u32⟩,⟨683951853#u32,2048694542#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
def v2 : E := ⟨⟨⟨891788758#u32,435047592#u32⟩,⟨1067086591#u32,1303482137#u32⟩⟩,⟨⟨1713231283#u32,659744118#u32⟩,⟨1902473248#u32,500785724#u32⟩⟩⟩
def v3 : E := ⟨⟨⟨1278631975#u32,934676002#u32⟩,⟨1052168638#u32,466298167#u32⟩⟩,⟨⟨313826527#u32,1069894547#u32⟩,⟨1078108256#u32,1855025080#u32⟩⟩⟩
def v4 : E := ⟨⟨⟨1181025707#u32,1313346478#u32⟩,⟨236793317#u32,1984744021#u32⟩⟩,⟨⟨2111656893#u32,304649819#u32⟩,⟨2022010304#u32,865135617#u32⟩⟩⟩
def value : E := ⟨⟨⟨1905869162#u32,1402078443#u32⟩,⟨596069241#u32,1033056917#u32⟩⟩,⟨⟨1064785135#u32,1686775190#u32⟩,⟨505502576#u32,753154816#u32⟩⟩⟩
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
end AspisR1.JGs_S11
end
