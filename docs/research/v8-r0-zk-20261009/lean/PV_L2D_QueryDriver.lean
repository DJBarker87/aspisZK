import PV_L2D_QueryBounds
set_option autoImplicit false
namespace PV_L2D_QueryDriver
open PV_L2D_QueryScan PV_L2D_QueryBounds

structure Driven where
  selected : Nat
  state : State
  scanned : Nat
  deriving DecidableEq, Repr

/-- All eight block/advance pairs were eagerly generated before this driver.
The default final advance is 7; the early-stop check is inside scan. -/
def drive : Nat → State → List (List Nat) → Driven
  | _,s,[] => ⟨7,s,0⟩
  | k,s,x::xs =>
    let a:=scan s x
    if a.1 then ⟨k,a.2,1⟩ else
      let b:=drive (k+1) a.2 xs
      ⟨b.selected,b.state,b.scanned+1⟩

inductive Result where
  | success (queries : List Nat) (selected : Nat)
  | exhausted (accepted : Nat)
  deriving DecidableEq, Repr

def finish (a : Driven) : Result :=
  if a.state.accepted.length=22 then .success a.state.accepted a.selected
  else .exhausted a.state.accepted.length

theorem scan_count (k : Nat) (s : State) (blocks : List (List Nat)) :
    (drive k s blocks).scanned≤blocks.length := by
  induction blocks generalizing k s with
  | nil => simp [drive]
  | cons x xs ih =>
    have h:=ih (k+1) (scan s x).2
    simp only [drive]
    split <;> simp_all
#print axioms scan_count

theorem drive_admitted (k : Nat) (s : State) (blocks : List (List Nat))
    (h : Admitted s) (small : ∀ xs∈blocks,∀ x∈xs,x<2^18) :
    Admitted (drive k s blocks).state := by
  induction blocks generalizing k s with
  | nil => exact h
  | cons xs blocks ih =>
    have hs:=scan_admitted s xs h (small xs (by simp))
    simp only [drive]
    split
    · exact hs
    · exact ih (k+1) (scan s xs).2 hs (fun ys hy=>small ys (by simp [hy]))
#print axioms drive_admitted

theorem success_shape (a : Driven) (qs : List Nat) (k : Nat)
    (h : finish a=.success qs k) : qs=a.state.accepted ∧ qs.length=22 ∧ k=a.selected := by
  unfold finish at h
  split at h
  · cases h
    exact ⟨rfl,by assumption,rfl⟩
  · contradiction
#print axioms success_shape

theorem selected_range (k : Nat) (s : State) (blocks : List (List Nat)) :
    (drive k s blocks).selected=7 ∨
    k≤(drive k s blocks).selected ∧ (drive k s blocks).selected<k+blocks.length := by
  induction blocks generalizing k s with
  | nil => simp [drive]
  | cons x xs ih =>
    have h:=ih (k+1) (scan s x).2
    simp only [drive]
    split
    · simp
    · simp only [List.length_cons]
      rcases h with h|h
      · exact Or.inl h
      · exact Or.inr ⟨by omega,by omega⟩
#print axioms selected_range

/-- Filling at exactly a block end does not trigger a post-block guard.
The next nonempty block performs the stop check and selects its advance. -/
theorem block_boundary (s : State) (xs ys : List Nat) (k : Nat)
    (hscan : scan s xs=(false,⟨List.range 22,22⟩))
    (nonempty : ys≠[]) : (drive k s [xs,ys]).selected=k+1 := by
  cases ys with
  | nil => contradiction
  | cons y ys => simp [drive,hscan,scan,stopped]
#print axioms block_boundary

theorem empty_exhaustion : finish (drive 0 ⟨[],0⟩ [])=.exhausted 0 := by decide
#print axioms empty_exhaustion
end PV_L2D_QueryDriver
