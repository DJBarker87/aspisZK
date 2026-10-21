import R1Z.ProverCommitExtractedCoin27
/-! Exact generated call equation, including wrapping machine cursor and the
map contract's prior value. The Nat-view theorem separately requires room. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitCoinCall27
open Aeneas Aeneas.Std Result AspisR1CoinEffect27
open ProverCommitCoinTape27 ProverCommitExtractedCoin27
attribute [local instance] Classical.propDecidable
abbrev Bytes32 := Array U8 32#usize
abbrev Table := List UInt8 → Option Bytes32
local instance : DecidableEq Bytes32 := Classical.decEq _
abbrev Machine := CoinState Table

def mapRecording : Recording Table where
  insert table parts answer := ok (insert table (ProverCommitStreamBytes.wireBytes parts) answer)

def answer (s : Machine) : Bytes32 :=
  (s.coins.val[s.next.val]?).getD (Array.repeat 32#usize 0#u8)

def view (s : Machine) : State (List UInt8) Bytes32 :=
  ⟨fun n => (s.coins.val[n]?).getD (Array.repeat 32#usize 0#u8),
    s.next.val,s.record,s.collision⟩

def expected (s : Machine) (parts : ProverCommitOracleEffect26.Parts) : Bytes32 × Machine :=
  let effects := (reference (view s) (ProverCommitStreamBytes.wireBytes parts)).2
  (answer s,{s with next := Usize.wrapping_add s.next 1#usize, record := effects.record,collision := effects.collision})

theorem read_total (s : Machine) :
    (if s.next < alloc.vec.Vec.len s.coins then
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Bytes32) s.coins s.next
    else ok (Array.repeat 32#usize 0#u8)) = ok (answer s) := by
  by_cases h : s.next.val < s.coins.val.length
  · have cond : s.next < alloc.vec.Vec.len s.coins := h
    rw [if_pos cond,alloc.vec.Vec.index_slice_index]
    simp only [alloc.vec.Vec.index_usize,alloc.vec.Vec.getElem?_Nat_eq,
      List.getElem?_eq_getElem h,answer,Option.getD_some]
  · have cond : ¬ s.next < alloc.vec.Vec.len s.coins := h
    rw [if_neg cond]
    simp only [answer,List.getElem?_eq_none (by omega : s.coins.val.length ≤ s.next.val),Option.getD_none]

/-- Exact generated body, for every finite vector length and every cursor.
Machine overflow is retained here instead of silently assuming it away. -/
theorem call_exact (s : Machine) (parts : ProverCommitOracleEffect26.Parts) :
    CoinOracle.Insts.Effect27EffectDigest32CoinState.digest mapRecording s parts =
      ok (expected s parts) := by
  simp only [CoinOracle.Insts.Effect27EffectDigest32CoinState.digest,read_total,bind_tc_ok,lift]
  cases rec : s.record with
  | none => simp [core.option.Option.take,rec,expected,view,reference,answer]
  | some table =>
    cases previous : table (ProverCommitStreamBytes.wireBytes parts) with
    | none => simp [core.option.Option.take,rec,mapRecording,ProverCommitCoinTape27.insert,previous,expected,view,reference,answer]
    | some old =>
      by_cases same : old = answer s
      · simp only [answer] at same
        simp [core.option.Option.take,rec,mapRecording,ProverCommitCoinTape27.insert,previous,different_eq,same,expected,view,reference,answer]
      · simp only [answer] at same
        simp [core.option.Option.take,rec,mapRecording,ProverCommitCoinTape27.insert,previous,different_eq,same,expected,view,reference,answer]

#print axioms read_total
#print axioms call_exact
end R1Z.ProverCommitCoinCall27
