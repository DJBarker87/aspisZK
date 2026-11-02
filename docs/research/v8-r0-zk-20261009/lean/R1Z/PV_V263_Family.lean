import R1Z.PV_V263_WorkerControl
import R1Z.PV_V263_PublicRequests
/-! Inner host_work range/callback traversal. This component keeps a stateful
callback, the inner capacity site, TLS restoration and caught panics. It does
not yet interpret std's outer collect/Vec growth, scheduler or drop glue. -/
set_option autoImplicit false
namespace R1Z.PV_V263_Family
open Aeneas Aeneas.Std PV_V263_World PV_V263_WorkerRequests PV_V263_WorkerControl
open PV_V263_PublicRequests (Layout)
open PV_RunJoin_WorkRange35
open PV_RJ4IDB (Bytes)

def indices (n k : Nat) : List Nat := List.range' (start n k) (width n k)

def body {S A : Type} (runtime : Runtime S) (layout : Layout)
    (n k : Nat) (callback : Nat → Q S A) : Q S (List A) :=
  PV_V263_World.bind (runtime.answer (.allocate 0 k (width n k) layout.size layout.align)) fun _ =>
    traverse callback (indices n k)

def run {S A : Type} (runtime : Runtime S) (profile : Profile) (layout : Layout)
    (n k : Nat) (callback : Nat → Q S A) : Q S (Except Bytes (List A)) :=
  withActive runtime profile k (catchPanic profile (body runtime layout n k callback))

/-- No callback index can escape the original item count. This avoids reducing
any large reached vector, including the 14336-cell sumcheck range. -/
theorem in_range (n k i : Nat) (hk : k < 16) (hi : i ∈ indices n k) : i < n := by
  have hb := PV_RunJoin_WorkRange35.bounded n k hk
  simp only [indices,List.mem_range'] at hi
  omega

theorem traverse_total_on {S A : Type} (callback : Nat → Q S A) (is : List Nat)
    (law : ∀ i, i ∈ is → ∀ w, ∃ a, (callback i w).outcome = .returned (.ok a))
    (w : State S) :
    ∃ values, (traverse callback is w).outcome = .returned (.ok values) := by
  induction is generalizing w with
  | nil => exact ⟨[],rfl⟩
  | cons i is ih =>
    obtain ⟨a,ha⟩ := law i (by simp) w
    obtain ⟨rest,hr⟩ := ih (fun j hj v => law j (by simp only [List.mem_cons]; exact Or.inr hj) v) (callback i w).state
    exact ⟨a::rest,by simp only [traverse,PV_V263_World.bind,ha,hr,PV_V263_World.lift]⟩

/-- Resources are derived from grants; the only hypothesis concerns callback
execution and must still be proved for actual captured instantiations. This
is a conditional component theorem, not a new endpoint success premise. -/
theorem granting_body {S A : Type} (encode : {B : Type} → Request B → Bytes)
    (layout : Layout) (n k : Nat) (hk : k < 16) (callback : Nat → Q S A)
    (law : ∀ i, i < n → ∀ w, ∃ a, (callback i w).outcome = .returned (.ok a))
    (w : State S) :
    ∃ values, (body (grants encode) layout n k callback w).outcome = .returned (.ok values) := by
  obtain ⟨values,h⟩ := traverse_total_on callback (indices n k)
    (fun i hi v => law i (in_range n k i hk hi) v) w
  exact ⟨values,by simpa only [body,PV_V263_World.bind,grants] using h⟩

/-- The inner allocation is an explicit request even for count zero. Whether
its zero capacity causes an allocator call is a separate std lowering fact. -/
theorem capacity (n k : Nat) (layout : Layout) :
    (PV_V263_PublicRequests.bytes (.item k (width n k) layout)) = width n k * layout.size := rfl

#print axioms indices
#print axioms body
#print axioms run
#print axioms in_range
#print axioms traverse_total_on
#print axioms granting_body
#print axioms capacity
end R1Z.PV_V263_Family
