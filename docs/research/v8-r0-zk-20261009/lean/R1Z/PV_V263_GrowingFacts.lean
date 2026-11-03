import R1Z.PV_V263_GrowingPush
/-! Exact outcome/post-world laws at the growing push boundary. An allocator
answer is requested before the new pointer/capacity or the pushed value is
committed; no callback-success or actual-capture premise occurs here. -/
set_option autoImplicit false
namespace R1Z.PV_V263_GrowingFacts
open Aeneas Aeneas.Std PV_V263_World PV_V263_OwnedDrain PV_V263_RawGrowth

theorem grows_fault {S A : Type} (runtime : Runtime S) (out : Owner A) (a : A)
    (full : out.initialized.values.length=capacity out.allocation)
    (sized : out.allocation.layout.size≠0)
    (bounded : requestedCap out.allocation.layout.size out.allocation.rawCapacity≤Usize.max ∧
      requestedCap out.allocation.layout.size out.allocation.rawCapacity*out.allocation.layout.size≤Usize.max/2)
    (w : State S) (error : Fault)
    (h : (runtime.resize ⟨release out.allocation,
      requestedCap out.allocation.layout.size out.allocation.rawCapacity*out.allocation.layout.size,
      out.allocation.layout.align⟩ w).outcome=.fault error) :
    PV_V263_GrowingPush.push runtime out a w=⟨.fault error,
      (runtime.resize ⟨release out.allocation,
        requestedCap out.allocation.layout.size out.allocation.rawCapacity*out.allocation.layout.size,
        out.allocation.layout.align⟩ w).state,
      (runtime.resize ⟨release out.allocation,
        requestedCap out.allocation.layout.size out.allocation.rawCapacity*out.allocation.layout.size,
        out.allocation.layout.align⟩ w).events⟩ := by
  simp only [PV_V263_GrowingPush.push,dif_pos full,dif_neg sized,dif_pos bounded,
    PV_V263_World.bind,h]

theorem grows_success {S A : Type} (runtime : Runtime S) (out : Owner A) (a : A)
    (full : out.initialized.values.length=capacity out.allocation)
    (sized : out.allocation.layout.size≠0)
    (bounded : requestedCap out.allocation.layout.size out.allocation.rawCapacity≤Usize.max ∧
      requestedCap out.allocation.layout.size out.allocation.rawCapacity*out.allocation.layout.size≤Usize.max/2)
    (w : State S) (pointer : Nat)
    (h : (runtime.resize ⟨release out.allocation,
      requestedCap out.allocation.layout.size out.allocation.rawCapacity*out.allocation.layout.size,
      out.allocation.layout.align⟩ w).outcome=.returned (.ok pointer)) :
    ∃ next, PV_V263_GrowingPush.push runtime out a w=⟨.returned (.ok next),
      (runtime.resize ⟨release out.allocation,
        requestedCap out.allocation.layout.size out.allocation.rawCapacity*out.allocation.layout.size,
        out.allocation.layout.align⟩ w).state,
      (runtime.resize ⟨release out.allocation,
        requestedCap out.allocation.layout.size out.allocation.rawCapacity*out.allocation.layout.size,
        out.allocation.layout.align⟩ w).events⟩ ∧
      next.initialized.values.val=out.initialized.values.val++[a] ∧
      next.allocation.pointer=pointer ∧
      next.allocation.rawCapacity=requestedCap out.allocation.layout.size out.allocation.rawCapacity ∧
      next.allocation.layout=out.allocation.layout := by
  simp only [PV_V263_GrowingPush.push,dif_pos full,dif_neg sized,dif_pos bounded,
    PV_V263_World.bind,h,PV_V263_World.lift,List.append_nil]
  exact ⟨_,rfl,rfl,rfl,rfl,rfl⟩

#print axioms grows_fault
#print axioms grows_success
end R1Z.PV_V263_GrowingFacts
