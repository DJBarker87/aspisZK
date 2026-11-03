import R1Z.PV_V263_RawGrowth
/-! Stateful Vec push including the actual grow_one branch. Reserved stores
have no resource request; the growth branch requests a new pointer before
storing the moved value and committing the new descriptor. The typed value
copy is not yet a byte-heap proof of Global::grow. -/
set_option autoImplicit false
namespace R1Z.PV_V263_GrowingPush
open Aeneas Aeneas.Std PV_V263_World PV_V263_OwnedDrain PV_V263_RawGrowth

def push {S A : Type} (runtime : Runtime S) (out : Owner A) (a : A) : Q S (Owner A) :=
  if full : out.initialized.values.length=capacity out.allocation then
    if zero : out.allocation.layout.size=0 then runtime.overflow
    else
      let cap := requestedCap out.allocation.layout.size out.allocation.rawCapacity
      if bounded : cap≤Usize.max ∧ cap*out.allocation.layout.size≤Usize.max/2 then
        PV_V263_World.bind
          (runtime.resize ⟨release out.allocation,cap*out.allocation.layout.size,out.allocation.layout.align⟩)
          (fun pointer =>
            let allocation : Allocation := ⟨pointer,cap,out.allocation.layout,bounded.1⟩
            have room : out.initialized.values.length+1≤cap := by
              have raw : out.initialized.values.length=out.allocation.rawCapacity := by
                simpa only [capacity,zero,if_false] using full
              rw [raw]
              exact enough _ _
            let buffer : PV_V263_VectorDrain.Buffer A :=
              ⟨out.initialized.values,cap,by omega,bounded.1⟩
            let grown : Owner A := ⟨buffer,allocation,by
              simp only [allocation,capacity,zero,if_false]; exact Nat.le_refl _⟩
            lift (.ok (store grown a (by
              simpa only [grown,allocation,capacity,zero,if_false] using room))))
      else runtime.overflow
  else
    have room : out.initialized.values.length+1≤capacity out.allocation := by
      have fits := out.initialized.fits.trans out.reserved
      omega
    lift (.ok (store out a room))

theorem reserved {S A : Type} (runtime : Runtime S) (out : Owner A) (a : A)
    (room : out.initialized.values.length+1≤capacity out.allocation) (w : State S) :
    push runtime out a w=⟨.returned (.ok (store out a room)),w,[]⟩ := by
  have notFull : out.initialized.values.length≠capacity out.allocation := by omega
  simp only [push,dif_neg notFull,PV_V263_World.lift]

/-- Contents, physical capacity and pointer remain intact when no growth is
needed, even if the original reservation was only a strict lower bound. -/
theorem reserved_values {S A : Type} (runtime : Runtime S) (out : Owner A) (a : A)
    (room : out.initialized.values.length+1≤capacity out.allocation) (w : State S) :
    ∃ next, push runtime out a w=⟨.returned (.ok next),w,[]⟩ ∧
      next.initialized.values.val=out.initialized.values.val++[a] ∧
      next.allocation=out.allocation :=
  ⟨store out a room,reserved runtime out a room w,(store_values out a room).1,
    (store_values out a room).2⟩

#print axioms push
#print axioms reserved
#print axioms reserved_values
end R1Z.PV_V263_GrowingPush
