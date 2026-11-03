import R1Z.PV_V263_OwnedPush
import R1Z.PV_V263_World
/-! Rust 1.94.1 grow_one/grow_amortized request planning. A reserved push
does not consult the allocator. A growing push retains the old descriptor
until the allocation answer succeeds. Native byte-heap interpretation and
Global allocator association are separate obligations. -/
set_option autoImplicit false
namespace R1Z.PV_V263_RawGrowth
open Aeneas Aeneas.Std PV_V263_World PV_V263_OwnedDrain
abbrev Layout := PV_V263_PublicRequests.Layout

def minCap (size : Nat) : Nat := if size=1 then 8 else if size≤1024 then 4 else 1

def requestedCap (size raw : Nat) : Nat := max (minCap size) (max (raw*2) (raw+1))

structure Resize where
  old : Option (Nat × Nat × Nat)
  bytes : Nat
  align : Nat
 deriving DecidableEq

inductive Decision where
  | reserved
  | overflow
  | grow (cap : Nat) (request : Resize)
 deriving DecidableEq

/-- Vec::push_mut calls grow_one only at equality; grow_one passes RAW cap
as len and 1 as additional. layout_array checks the isize byte bound. The
extra explicit cap check is redundant for nonzero element size, proved below. -/
def plan (allocation : Allocation) (length : Nat) : Decision :=
  if length≠capacity allocation then .reserved
  else if allocation.layout.size=0 then .overflow
  else
    let cap := requestedCap allocation.layout.size allocation.rawCapacity
    if cap≤Usize.max ∧ cap*allocation.layout.size≤Usize.max/2 then
      .grow cap ⟨release allocation,cap*allocation.layout.size,allocation.layout.align⟩
    else .overflow

structure Runtime (S : Type) where
  resize : Resize → Q S Nat
  overflow : {A : Type} → Q S A

/-- Store into the physical capacity, retaining its exact allocation. -/
def store {A : Type} (out : Owner A) (a : A)
    (room : out.initialized.values.length+1≤capacity out.allocation) : Owner A :=
  let buffer : PV_V263_VectorDrain.Buffer A :=
    ⟨out.initialized.values,capacity out.allocation,
      out.initialized.fits.trans out.reserved,capacity_bound out.allocation⟩
  ⟨PV_V263_BufferLoop.stored buffer a room,out.allocation,Nat.le_refl _⟩

def grow {S : Type} (runtime : Runtime S) (allocation : Allocation) : Q S Allocation :=
  if zero : allocation.layout.size=0 then runtime.overflow
  else
    let cap := requestedCap allocation.layout.size allocation.rawCapacity
    if bounded : cap≤Usize.max ∧ cap*allocation.layout.size≤Usize.max/2 then
      PV_V263_World.bind
        (runtime.resize ⟨release allocation,cap*allocation.layout.size,allocation.layout.align⟩)
        (fun pointer => lift (.ok ⟨pointer,cap,allocation.layout,bounded.1⟩))
    else runtime.overflow

theorem byte_bound_implies_cap (size cap : Nat) (sized : 0<size)
    (bytes : cap*size≤Usize.max/2) : cap≤Usize.max := by
  have h : cap≤cap*size := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left cap sized
  exact h.trans (bytes.trans (Nat.div_le_self _ _))

theorem enough (size raw : Nat) : raw+1≤requestedCap size raw :=
  (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

theorem reserved_no_request (allocation : Allocation) (length : Nat)
    (room : length+1≤capacity allocation) : plan allocation length=.reserved := by
  have ne : length≠capacity allocation := by omega
  simp only [plan,ne,if_true]

theorem zero_overflow (allocation : Allocation) (zero : allocation.layout.size=0) :
    plan allocation Usize.max=.overflow := by
  simp only [plan,capacity,zero,if_true,ne_eq,not_true_eq_false,if_false]

theorem store_values {A : Type} (out : Owner A) (a : A)
    (room : out.initialized.values.length+1≤capacity out.allocation) :
    (store out a room).initialized.values.val=out.initialized.values.val++[a] ∧
    (store out a room).allocation=out.allocation := ⟨rfl,rfl⟩

/-- An allocation fault retains its own world/event prefix; no pointer or
capacity is committed by the subsequent source assignment. -/
theorem grow_fault {S : Type} (runtime : Runtime S) (allocation : Allocation)
    (sized : allocation.layout.size≠0)
    (bounded : requestedCap allocation.layout.size allocation.rawCapacity≤Usize.max ∧
      requestedCap allocation.layout.size allocation.rawCapacity*allocation.layout.size≤Usize.max/2)
    (w : State S) (error : Fault)
    (h : (runtime.resize ⟨release allocation,
      requestedCap allocation.layout.size allocation.rawCapacity*allocation.layout.size,
      allocation.layout.align⟩ w).outcome=.fault error) :
    grow runtime allocation w=⟨.fault error,
      (runtime.resize ⟨release allocation,
        requestedCap allocation.layout.size allocation.rawCapacity*allocation.layout.size,
        allocation.layout.align⟩ w).state,
      (runtime.resize ⟨release allocation,
        requestedCap allocation.layout.size allocation.rawCapacity*allocation.layout.size,
        allocation.layout.align⟩ w).events⟩ := by
  simp only [grow,dif_neg sized,dif_pos bounded,PV_V263_World.bind,h]

#print axioms minCap
#print axioms requestedCap
#print axioms plan
#print axioms store
#print axioms grow
#print axioms byte_bound_implies_cap
#print axioms enough
#print axioms reserved_no_request
#print axioms zero_overflow
#print axioms store_values
#print axioms grow_fault
end R1Z.PV_V263_RawGrowth
