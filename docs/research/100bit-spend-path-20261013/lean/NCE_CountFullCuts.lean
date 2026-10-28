import NCE_CountLevelCuts
import NCE_CountInitCuts

set_option autoImplicit false
namespace AspisR1.NCE_CountFullCuts
open NCE_CountCuts NCE_CountRowCuts NCE_CountLevelCuts NCE_CountInitCuts
open MultiproofConeCountPhysical OraclePortFrozenOrder

def levels {Frame : Type}
    (scan : ScanState (Nat × Frame) → Bool × ScanState (Nat × Frame))
    (store : RowState (Nat × Frame) → Nat → RowState (Nat × Frame))
    (height : RowState (Nat × Frame) → LevelState Frame) : Nat → LevelState Frame → LevelState Frame
  | 0,s => s
  | fuel+1,s => levels scan store height fuel (level scan store height s)

/-- Height induction from scan/store/height ONE-step native cuts. Each next
level consumes the actual previous returned private array. Its domains are
outputs of the existing checked level projection, never extra premises. -/
theorem levels_port {Frame : Type}
    (scan : ScanState (Nat × Frame) → Bool × ScanState (Nat × Frame))
    (scanCut : NCE_Native_CountScan scan)
    (store : RowState (Nat × Frame) → Nat → RowState (Nat × Frame))
    (storeCut : NCE_Native_CountCommit store)
    (height : RowState (Nat × Frame) → LevelState Frame)
    (heightCut : NCE_Native_CountHeight height) (fuel : Nat) (s : LevelState Frame)
    (span : s.depth+fuel ≤ 18) (small : s.n ≤ 16)
    (order : (cells s.key 0 s.n).Pairwise (·<·))
    (range : ∀ k, k < s.n → s.key k < 262144) (spent : s.count ≤ 16*s.depth) :
    let out := levels scan store height fuel s
    out.count = s.count+nodeCount fuel (cells s.key 0 s.n) ∧
    out.frame = s.frame ∧ out.depth = s.depth+fuel := by
  induction fuel generalizing s with
  | zero => exact ⟨by simp only [levels,nodeCount,Nat.add_zero],rfl,by simp only [levels,Nat.add_zero]⟩
  | succ fuel ih =>
    let next := level scan store height s
    obtain ⟨front,total,depth,frame,size,ordered,keys,used⟩ :=
      level_port scan scanCut store storeCut height heightCut s (by omega) small order range spent
    have enough : next.depth+fuel ≤ 18 := by change (level scan store height s).depth+fuel ≤ 18; rw [depth]; omega
    have tail := ih next enough size ordered keys used
    have length : (cells s.key 0 s.n).length = s.n := by simp only [cells,List.length_map,List.length_range]
    change (levels scan store height fuel next).count =
      s.count+nodeCount (fuel+1) (cells s.key 0 s.n) ∧
      (levels scan store height fuel next).frame = s.frame ∧
      (levels scan store height fuel next).depth = s.depth+(fuel+1)
    refine ⟨?_,tail.2.1.trans frame,?_⟩
    · rw [tail.1,total,front,nodeCount,length]
      omega
    · have afterDepth := tail.2.2
      rw [depth] at afterDepth
      omega

/-- The actual initialized native count carrier is constructed from the
zero and one-window copy cuts before the eighteen source levels. This theorem
establishes the count VALUE and caller frame conditional on those cuts.
It does not supply native admission/outer-control association or claim that
its structural denotation is already the shipped node_count function. -/
theorem initialized_eighteen {Frame : Type}
    (create : (Nat → Nat) → Nat → Frame → InitState Frame)
    (zeroCut : NCE_Native_CountZero create) (copy : InitState Frame → InitState Frame)
    (copyCut : NCE_Native_CountCopy copy)
    (scan : ScanState (Nat × Frame) → Bool × ScanState (Nat × Frame))
    (scanCut : NCE_Native_CountScan scan)
    (store : RowState (Nat × Frame) → Nat → RowState (Nat × Frame))
    (storeCut : NCE_Native_CountCommit store)
    (height : RowState (Nat × Frame) → LevelState Frame)
    (heightCut : NCE_Native_CountHeight height)
    (key : Nat → Nat) (n : Nat) (frame : Frame) (small : n ≤ 16)
    (order : (cells key 0 n).Pairwise (·<·))
    (range : ∀ k, k < n → key k < 262144) :
    let initialized := run copy n (create key n frame)
    let out := levels scan store height 18 ⟨initialized.memory,initialized.n,0,0,initialized.frame⟩
    out.count = MultiproofConeCountLevels.sourceCount 18 (cells key 0 n) ∧ out.frame = frame := by
  rw [NCE_CountInitCuts.initialized create zeroCut copy copyCut key n frame small range]
  dsimp only
  let initial : LevelState Frame := ⟨NBV_CountInitialization.initialized key n,n,0,0,frame⟩
  have initialOrder : (cells initial.key 0 initial.n).Pairwise (·<·) := by
    change (cells (NBV_CountInitialization.initialized key n) 0 n).Pairwise (·<·)
    rw [NBV_CountInitialization.initialized_live]
    exact order
  have initialRange : ∀ k, k < initial.n → initial.key k < 262144 := by
    intro k kb
    change NBV_CountInitialization.initialized key n k < 262144
    rw [NBV_CountInitialization.initialized_cell,if_pos kb]
    exact range k kb
  have result := levels_port scan scanCut store storeCut height heightCut 18 initial
    (by change 0+18 ≤ 18; omega) small initialOrder initialRange (Nat.le_refl 0)
  have counted := result.1
  change (levels scan store height 18 initial).count = 0+nodeCount 18
    (cells (NBV_CountInitialization.initialized key n) 0 n) at counted
  rw [Nat.zero_add,NBV_CountInitialization.initialized_live,
    ←MultiproofConeCountLevels.count_eq 18 (cells key 0 n) order] at counted
  exact ⟨counted,result.2.1⟩

#print axioms levels_port
#print axioms initialized_eighteen
end AspisR1.NCE_CountFullCuts
