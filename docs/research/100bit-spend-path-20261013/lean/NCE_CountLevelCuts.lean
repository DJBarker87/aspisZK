import NCE_CountRowCuts

set_option autoImplicit false
namespace AspisR1.NCE_CountLevelCuts
open NCE_CountCuts NCE_CountRowCuts
open MultiproofConeCountPhysical MultiproofConeLiveOrder OraclePortFrozenOrder

structure LevelState (Frame : Type) where
  key : Nat → Nat
  n : Nat
  count : Nat
  depth : Nat
  frame : Frame

/-- ONE native outer transition: preserve the returned private key carrier,
set n=w, and advance the finite height counter. No next-level result. -/
def NCE_Native_CountHeight {Frame : Type}
    (native : RowState (Nat × Frame) → LevelState Frame) : Prop :=
  ∀ s, s.w ≤ 16 → s.frame.1 < 18 →
    (∀ k, (native s).key k = s.key k) ∧ (native s).n = s.w ∧
    (native s).count = s.count ∧ (native s).depth = s.frame.1+1 ∧
    (native s).frame = s.frame.2

def advance {Frame : Type} (s : RowState (Nat × Frame)) : LevelState Frame :=
  ⟨s.key,s.w,s.count,s.frame.1+1,s.frame.2⟩

theorem advance_eq {Frame : Type}
    (native : RowState (Nat × Frame) → LevelState Frame)
    (cut : NCE_Native_CountHeight native) (s : RowState (Nat × Frame))
    (small : s.w ≤ 16) (height : s.frame.1 < 18) : native s = advance s := by
  obtain ⟨keys,n,count,depth,frame⟩ := cut s small height
  have key : (native s).key = s.key := funext keys
  cases s with
  | mk sk sn si sw sc sf =>
    cases h : native (RowState.mk sk sn si sw sc sf) with
    | mk nk nn nc nd nf =>
      simp only [h] at key n count depth frame
      cases key
      cases n
      cases count
      cases depth
      cases frame
      rfl

def level {Frame : Type} (scan : ScanState (Nat × Frame) → Bool × ScanState (Nat × Frame))
    (store : RowState (Nat × Frame) → Nat → RowState (Nat × Frame))
    (height : RowState (Nat × Frame) → LevelState Frame) (s : LevelState Frame) : LevelState Frame :=
  height (rows scan store s.n ⟨s.key,s.n,0,0,s.count,(s.depth,s.frame)⟩)

/-- One complete count level consumes the already checked row association.
It returns the actual next private key carrier; all native height domains are
derived from the old level's source projection and frame. -/
theorem level_port {Frame : Type}
    (scan : ScanState (Nat × Frame) → Bool × ScanState (Nat × Frame))
    (scanCut : NCE_Native_CountScan scan)
    (store : RowState (Nat × Frame) → Nat → RowState (Nat × Frame))
    (storeCut : NCE_Native_CountCommit store)
    (height : RowState (Nat × Frame) → LevelState Frame)
    (heightCut : NCE_Native_CountHeight height) (s : LevelState Frame)
    (depth : s.depth < 18) (small : s.n ≤ 16)
    (order : (cells s.key 0 s.n).Pairwise (·<·))
    (range : ∀ k, k < s.n → s.key k < 262144)
    (spent : s.count ≤ 16*s.depth) :
    let out := level scan store height s
    let expected := countLevel s.n (cells s.key 0 s.n)
    cells out.key 0 out.n = expected.1 ∧ out.count = s.count+expected.2 ∧
    out.depth = s.depth+1 ∧ out.frame = s.frame ∧ out.n ≤ 16 ∧
    (cells out.key 0 out.n).Pairwise (·<·) ∧
    (∀ k, k < out.n → out.key k < 262144) ∧ out.count ≤ 16*out.depth := by
  let entry : RowState (Nat × Frame) := ⟨s.key,s.n,0,0,s.count,(s.depth,s.frame)⟩
  let after := rows scan store s.n entry
  have port := rows_port scan scanCut store storeCut s.n s.depth entry depth small
    (Nat.le_refl 0) (Nat.zero_le _) (NBJ_CountLevels.strict_cells s.key s.n order) range (by simpa only [entry,Nat.add_zero] using spent)
  have shifted := NBY_CountCarry.rows_shift s.n s.key s.n 0 0 0 s.count
  simp only [Nat.zero_add,NBJ_CountRows.level_port s.key s.n
    (NBJ_CountLevels.strict_cells s.key s.n order)] at shifted
  have result : (cells after.key 0 after.w,after.count) =
      ((countLevel s.n (cells s.key 0 s.n)).1,(countLevel s.n (cells s.key 0 s.n)).2+s.count) :=
    port.1.trans shifted
  have front : cells after.key 0 after.w = (countLevel s.n (cells s.key 0 s.n)).1 := congrArg Prod.fst result
  have total : after.count = (countLevel s.n (cells s.key 0 s.n)).2+s.count := congrArg Prod.snd result
  have frame : after.frame = (s.depth,s.frame) := port.2
  have length : (cells after.key 0 after.w).length = after.w := by simp only [cells,List.length_map,List.length_range]
  have inputLength : (cells s.key 0 s.n).length = s.n := by simp only [cells,List.length_map,List.length_range]
  have bounds := MultiproofConeCountBounds.level_bounds s.n (cells s.key 0 s.n)
  have width : after.w ≤ 16 := by rw [front] at length; omega
  have next := MultiproofConeCountPhysicalLevels.next_domain (cells s.key 0 s.n)
    order (by simpa only [inputLength] using small) (by
      intro value mem
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp mem
      have kb : k < s.n := List.mem_range.mp hk
      simpa only [Nat.zero_add] using range k kb)
  rw [inputLength] at next
  have advanceDomain : after.frame.1 < 18 := by rw [frame]; exact depth
  have levelEq : level scan store height s = advance after := advance_eq height heightCut after width advanceDomain
  dsimp only
  rw [levelEq]
  dsimp only [advance]
  refine ⟨front,by omega,by rw [frame],by rw [frame],width,?_,?_,?_⟩
  · rw [front]; exact next.1
  · intro k kb
    apply next.2.2
    rw [←front]
    apply List.mem_map.mpr
    exact ⟨k,List.mem_range.mpr kb,by simp only [Nat.zero_add]⟩
  · rw [frame]
    omega

#print axioms advance_eq
#print axioms level_port
end AspisR1.NCE_CountLevelCuts
