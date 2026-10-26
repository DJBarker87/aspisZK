import S6SnapshotBudgetV1
set_option autoImplicit false
namespace AspisS6AlignedAllocationRange
open AspisR1.S2W_D189Entry AspisR1.S2W_D189Wrappers

/-- Offset-only arithmetic of the owned Rust allocator reference, after the
initial cursor has been selected. Native word/pointer correspondence is a
separate checked boundary; this definition does not assert SDK equivalence. -/
def step (cursor bytes alignment : Nat) : Option Nat :=
  if bytes ≤ cursor then
    let next := ((cursor-bytes)/alignment)*alignment
    if 8 ≤ next then some next else none
  else none

structure Request where
  bytes : Nat
  alignment : Nat

def Valid (request : Request) : Prop :=
  0 < request.alignment ∧ request.alignment ≤ 8

def charge (requests : List Request) : Nat :=
  (requests.map (fun request => request.bytes+7)).sum

def reserve (cursor : Nat) : List Request → Option Nat
  | [] => some cursor
  | request::rest => (step cursor request.bytes request.alignment).bind
      (fun next => reserve next rest)

/-- One arbitrary step: rounding consumes at most7 bytes, the cursor header
remains reserved, and all intermediate offsets stay in the original arena. -/
theorem step_fits (cursor bytes alignment : Nat)
    (positive : 0 < alignment) (bounded : alignment ≤ 8)
    (fits : 8+bytes+7 ≤ cursor) :
    ∃ next, step cursor bytes alignment = some next ∧
      8 ≤ next ∧ next+bytes ≤ cursor ∧ cursor ≤ next+bytes+7 := by
  have remainder := Nat.mod_lt (cursor-bytes) positive
  have decomposition := Nat.mod_add_div (cursor-bytes) alignment
  rw [Nat.mul_comm alignment] at decomposition
  have byteFits : bytes ≤ cursor := by omega
  have header : 8 ≤ ((cursor-bytes)/alignment)*alignment := by omega
  refine ⟨((cursor-bytes)/alignment)*alignment,?_,header,?_,?_⟩
  · simp only [step,if_pos byteFits,if_pos header]
  · omega
  · omega

/-- Compose arbitrary many checked steps without normalizing any concrete
recurrence. No claim that live bytes are refunded by deallocation is used. -/
theorem reserve_fits (requests : List Request) (cursor : Nat)
    (valid : ∀ request ∈ requests, Valid request)
    (fits : 8+charge requests ≤ cursor) :
    ∃ next, reserve cursor requests = some next ∧
      8 ≤ next ∧ next ≤ cursor ∧ cursor ≤ next+charge requests := by
  induction requests generalizing cursor with
  | nil =>
    simp only [charge,List.map_nil,List.sum_nil] at fits
    exact ⟨cursor,rfl,fits,Nat.le_refl _,by simp [charge]⟩
  | cons request rest ih =>
    have current := valid request (by simp)
    have restValid : ∀ r ∈ rest, Valid r := by
      intro r member
      exact valid r (by simp [member])
    have charges : charge (request::rest) = request.bytes+7+charge rest := by
      simp [charge]
    obtain ⟨middle,first,header,decreasing,loss⟩ :=
      step_fits cursor request.bytes request.alignment current.1 current.2 (by omega)
    obtain ⟨next,tail,nextHeader,nextDecreasing,totalLoss⟩ :=
      ih middle restValid (by omega)
    refine ⟨next,?_,nextHeader,by omega,by omega⟩
    simp only [reserve,first,Option.bind_some,tail]

/-- Requests represented by the existing snapshot interface, with a
conservative alignment allowance for each individual request. -/
def snapshots (entry : Entry) : List Request :=
  (admittedSizes entry 3 firstSizes).map (fun bytes => ⟨bytes,1⟩)

theorem snapshot_charge (entry : Entry) : charge (snapshots entry) ≤ 61964 := by
  have size := AspisS6SnapshotBudget.first_snapshot_sum_bound entry
  have count : (admittedSizes entry 3 firstSizes).length ≤ 3 := by
    unfold admittedSizes
    have h := List.length_filterMap_le
      (fun a => let size := (entry.buffers (entry.handles a).1).val.length
                if size = (firstSizes a).1 ∨ size = (firstSizes a).2 then some size else none)
      (List.range 3)
    simpa using h
  have formula (sizes : List Nat) :
      charge (sizes.map (fun bytes => ⟨bytes,1⟩)) = sizes.sum+7*sizes.length := by
    induction sizes with
    | nil => simp [charge]
    | cons size rest ih =>
      simp only [List.map_cons,charge,List.sum_cons,List.length_cons] at *
      omega
  rw [snapshots,formula]
  omega

#print axioms step_fits
#print axioms reserve_fits
#print axioms snapshot_charge
end AspisS6AlignedAllocationRange
