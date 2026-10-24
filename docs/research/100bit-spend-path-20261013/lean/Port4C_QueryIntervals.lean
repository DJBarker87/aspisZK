import Port4C_QueryCounters
import Port4C_Pending

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_QueryIntervals
open Aeneas Aeneas.Std Result AspisR1Stage2

/-- Count terms relative to this block's constructor, including TX2's reset.
No terms=next hypothesis is made for the resumed block. -/
theorem block (ops : Port3_NativeQueryBody.Ops) (reserved : Bool)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights) (end1 : Usize)
    (weights : a.weights.val.length=64) (bound : a.next.val≤end1.val)
    (limit : end1.val≤22)
    (constructor : Port3_NativePendingInstall.source reserved a.weights.deref=ok (.Ok b))
    (accepted : Port3_QueryStage.query (Port3_NativeRowFrame.install ops)
      proof p a g none geometry b end1=ok (.Ok (out,bout))) :
    reserved=true ∧ bout.terms.val=end1.val-a.next.val ∧ out.next.val=end1.val := by
  have initial := Port4C_Pending.accepted reserved a.weights.deref b weights constructor
  have native := (Port3_QueryInstall.success_iff _ _).mp accepted
  have same : Port3_QueryStage.release (Port3_NativeRowFrame.install ops)=
      Port3_NativeRowFrame.install (Port3_QueryStage.release ops) := rfl
  rw [same] at native
  have count := Port4C_QueryCounters.loop_count (Port3_QueryStage.release ops)
    proof p a out g (Port3_QueryInstall.observer none) geometry b bout end1 weights
    initial.2.2.2.1 bound (by rw [initial.2.2.1]; change 0+_ < 256; omega) native
  refine ⟨initial.1,?_,count.2⟩
  simpa only [initial.2.2.1,show (0#usize).val=0 from rfl,Nat.zero_add] using count.1

/-- Both actual intervals in the installed current parent: terms10 then
terms12, rather than an erroneous resumed terms22. -/
theorem ten_twelve (ops : Port3_NativeQueryBody.Ops) (reserved : Bool)
    (proof : Slice U8) (p : verifier.Prepared) (a0 a10 a22 : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (geometry0 geometry1 : verifier.QueryGeometry)
    (b0 b10 b1 b12 : verifier.BatchedWeights)
    (size0 : a0.weights.val.length=64) (size1 : a10.weights.val.length=64)
    (start0 : a0.next.val=0) (start1 : a10.next.val=10)
    (new0 : Port3_NativePendingInstall.source reserved a0.weights.deref=ok (.Ok b0))
    (new1 : Port3_NativePendingInstall.source reserved a10.weights.deref=ok (.Ok b1))
    (run0 : Port3_QueryStage.query (Port3_NativeRowFrame.install ops)
      proof p a0 g none geometry0 b0 10#usize=ok (.Ok (a10,b10)))
    (run1 : Port3_QueryStage.query (Port3_NativeRowFrame.install ops)
      proof p a10 g none geometry1 b1 22#usize=ok (.Ok (a22,b12))) :
    b10.terms.val=10 ∧ b12.terms.val=12 ∧ a22.next.val=22 := by
  have first := block ops reserved proof p a0 a10 g geometry0 b0 b10 10#usize size0
    (by rw [start0]; decide) (by decide) new0 run0
  have second := block ops reserved proof p a10 a22 g geometry1 b1 b12 22#usize size1
    (by rw [start1]; decide) (by decide) new1 run1
  exact ⟨by have hf : b10.terms.val=10-a0.next.val := first.2.1; omega,
    by have hs : b12.terms.val=22-a10.next.val := second.2.1; omega,second.2.2⟩

#print axioms block
#print axioms ten_twelve
end AspisR1.Port4C_QueryIntervals
end
