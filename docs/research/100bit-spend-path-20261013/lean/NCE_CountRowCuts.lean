import NCE_CountCuts
import NBY_CountExecution

set_option autoImplicit false
namespace AspisR1.NCE_CountRowCuts
open NCE_CountCuts MultiproofConeCountPhysical MultiproofConeLiveOrder

/-- Private count scratch and its exact caller frame. This is the source
count loop's own level array, not a replacement for the verifier's scratch. -/
structure RowState (Frame : Type) where
  key : Nat → Nat
  n : Nat
  i : Nat
  w : Nat
  count : Nat
  frame : Frame

def CommitDomain {Frame : Type} (s : RowState Frame) (j : Nat) : Prop :=
  s.n ≤ 16 ∧ s.w ≤ s.i ∧ s.i < j ∧ j ≤ s.n ∧ j-s.i ≤ 2 ∧
    s.count+2 < 18446744073709551616 ∧
    ∀ k, k < s.n → s.key k < 262144

/-- Exactly the native post-scan scalar updates and one parent-index store. -/
def commit {Frame : Type} (s : RowState Frame) (j : Nat) : RowState Frame :=
  {s with key := write s.key s.i s.w, i := j, w := s.w+1, count := s.count+(2-(j-s.i))}

/-- Prospective ONE native count-commit cut. The arbitrary observed coordinate
provides the entire outside frame. No whole row scan or final count is assumed.
The Nat key function denotes the lifted finite native level array. -/
def NCE_Native_CountCommit {Frame : Type}
    (native : RowState Frame → Nat → RowState Frame) : Prop :=
  ∀ s j, CommitDomain s j →
    (∀ k, (native s j).key k = if k = s.w then s.key s.i / 2 else s.key k) ∧
    (native s j).n = s.n ∧ (native s j).i = j ∧
    (native s j).w = s.w+1 ∧ (native s j).count = s.count+(2-(j-s.i)) ∧
    (native s j).frame = s.frame

/-- One arbitrary-coordinate native store and its scalar frames identify the
exact inherited count write. No final-array identity is a hypothesis. -/
theorem commit_eq {Frame : Type} (native : RowState Frame → Nat → RowState Frame)
    (cut : NCE_Native_CountCommit native) (s : RowState Frame) (j : Nat)
    (domain : CommitDomain s j) : native s j = commit s j := by
  obtain ⟨keys,n,i,w,count,frame⟩ := cut s j domain
  have key : (native s j).key = write s.key s.i s.w := funext keys
  cases s with
  | mk sk sn si sw sc sf =>
    cases h : native (RowState.mk sk sn si sw sc sf) j with
    | mk nk nn ni nw nc nf =>
      simp only [h] at key n i w count frame
      cases key
      cases n
      cases i
      cases w
      cases count
      cases frame
      rfl

/-- Source order: test current row, execute the actual inner scan on its
prestate, commit once, then continue on that commit's returned key carrier. -/
def rows {Frame : Type} (scan : ScanState Frame → Bool × ScanState Frame)
    (store : RowState Frame → Nat → RowState Frame) : Nat → RowState Frame → RowState Frame
  | 0,s => s
  | fuel+1,s =>
      if s.i < s.n then
        let scanned := scanRun scan (s.n-s.i)
          ⟨s.key,s.n,s.key s.i/2,s.i,s.frame⟩
        rows scan store fuel (store {s with key:=scanned.key,frame:=scanned.frame} scanned.cursor)
      else s

/-- Conditional native-to-NBJ row association. This composes TWO narrow cuts:
the one-test scan and one post-scan commit. The next cut's finite domain is
proved from the inherited order, group-width and accumulator invariants. -/
theorem rows_port {Frame : Type}
    (scan : ScanState Frame → Bool × ScanState Frame)
    (scanCut : NCE_Native_CountScan scan)
    (store : RowState Frame → Nat → RowState Frame)
    (storeCut : NCE_Native_CountCommit store)
    (fuel depth : Nat) (s : RowState Frame)
    (height : depth < 18) (small : s.n ≤ 16) (safe : s.w ≤ s.i) (endBound : s.i ≤ s.n)
    (ordered : Strict s.key s.i s.n)
    (range : ∀ k, k < s.n → s.key k < 262144)
    (spent : s.count ≤ 16*depth+s.i) :
    let out := rows scan store fuel s
    (cells out.key 0 out.w,out.count) = NBJ_CountRows.nativeRows fuel s.key s.n s.i s.w s.count ∧
    out.frame = s.frame := by
  induction fuel generalizing s with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel ih =>
    by_cases active : s.i < s.n
    · have scanDomain := entry_domain s.key s.n s.i s.i s.frame small active endBound range
      have scanEq := scan_run_eq scan scanCut (s.n-s.i)
        (ScanState.mk s.key s.n (s.key s.i/2) s.i s.frame) scanDomain
      let j := NBI_CountScan.scan s.key (s.key s.i/2) s.n (s.n-s.i) s.i
      have group := NBI_CountScan.scan_group s.key s.n s.i active ordered
      have domain := NBI_CountScan.binary_group s.key s.n s.i active ordered
      have bounds : s.i < j ∧ j ≤ s.n ∧ 1 ≤ j-s.i ∧ j-s.i ≤ 2 := by
        dsimp only [j]
        rw [group.1]
        exact ⟨domain.1,domain.2.1,group.2.1,group.2.2⟩
      have machine := NBY_CountDomains.row_domain depth s.n s.i s.count height small active spent
      have commitDomain : CommitDomain s j :=
        ⟨small,safe,bounds.1,bounds.2.1,bounds.2.2.2,machine.2,range⟩
      have nextOrder : Strict (write s.key s.i s.w) j s.n := by
        intro a b lo asc hi
        have aw : a ≠ s.w := by omega
        have bw : b ≠ s.w := by omega
        simp only [write,if_neg aw,if_neg bw]
        exact ordered a b (by omega) asc hi
      have nextRange : ∀ k, k < s.n → (write s.key s.i s.w) k < 262144 := by
        intro k hk
        unfold write
        split
        · have value := range s.i active
          have divided := Nat.div_le_self (s.key s.i) 2
          omega
        · exact range k hk
      have nextSpent : s.count+(2-(j-s.i)) ≤ 16*depth+j :=
        NBY_CountDomains.row_preserves depth s.i j s.count
          ⟨bounds.2.2.1,bounds.2.2.2⟩ bounds.1 spent
      have tail := ih (commit s j) small (by change s.w+1 ≤ j; omega)
        bounds.2.1 nextOrder nextRange nextSpent
      rw [rows,if_pos active,scanEq]
      simp only
      rw [commit_eq store storeCut s j commitDomain]
      simp only [NBJ_CountRows.nativeRows,if_pos active]
      exact tail
    · simp [rows,NBJ_CountRows.nativeRows,active]

#print axioms commit_eq
#print axioms rows_port
end AspisR1.NCE_CountRowCuts
