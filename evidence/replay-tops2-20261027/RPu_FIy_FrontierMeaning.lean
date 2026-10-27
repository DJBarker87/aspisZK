import RPu_FIy_FrontierLoopStep
import RPu_FIy_FrontierBits
import RPu_FIy_EmptyRoot
import RPu_FIw_WordValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_FrontierMeaning
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIy_FrontierStep (Snapshot Selectors)

def roots (level : Nat) : Array U32 8#usize :=
  (pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1.val[level]?).getD
    (Array.repeat 8#usize 0#u32)
def frontier (src : Snapshot) (level : Nat) : Array U32 8#usize :=
  (src.frontier.val[level]?).getD (Array.repeat 8#usize 0#u32)
def rowValue (s : Selectors) (row : Nat) : K :=
  FIv_NativeArray.value s.high (row/16)*FIv_NativeArray.value s.low (row%16)
def zero (src : Snapshot) (level : Nat) : Prop := ((src.next_pair_index.val >>> level) &&& 1)=0
instance (src : Snapshot) (level : Nat) : Decidable (zero src level) := inferInstanceAs (Decidable (((src.next_pair_index.val >>> level) &&& 1)=0))
def increment (src : Snapshot) (s : Selectors) (a : Array NQ 16#usize) (level j : Nat) : K :=
  if zero src level then
    rowValue s ((34+level)*16)*(FIv_NativeArray.value a (8+j)-(FIy_DigestLane.target (roots level) true j : K))
  else rowValue s ((34+level)*16+12)*(FIv_NativeArray.value a j-(FIy_DigestLane.target (frontier src level) false j : K))

theorem zero_word (index : U64) : index=0#u64 ↔ index.val=0 := by
  constructor
  · intro h;rw [h];rfl
  · intro h;apply UScalar.eq_of_val_eq;exact h

theorem value (level : Usize) (a : Array NQ 16#usize) (s : Selectors)
    (d out : Array NQ 8#usize) (src : Snapshot) (hl : level.val<20)
    (ha : canonical a) (hh : canonical s.high) (hlo : canonical s.low) (hd : canonical d)
    (hf : ∀ row∈src.frontier.val,∀ x∈row.val,x.val<FIw_ScalarArithmetic.P)
    (success : FIy_FrontierStep.run level a s d src=ok out) :
    canonical out ∧ ∀ j : Fin (8#usize).val,
      decoded out j=decoded d j+increment src s a level.val j.val := by
  unfold FIy_FrontierStep.run at success
  obtain ⟨block,hblock,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨shifted,hshifted,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨bit,hbit,success⟩ := FIv_Map.bind_success _ _ _ success
  have blockValue := FIw_WordValue.add 34#usize level block hblock
  change block.val=34+level.val at blockValue
  have shiftValue := FIy_FrontierBits.shift src.next_pair_index level shifted hl hshifted
  have bitValue : bit.val=((src.next_pair_index.val >>> level.val) &&& 1) := by
    have eq : (shifted &&& 1#u64)=bit := Result.ok.inj hbit
    rw [←eq,UScalar.val_and,shiftValue]
    rfl
  have bitZero : bit=0#u64 ↔ zero src level.val := by rw [zero_word,bitValue];rfl
  split at success
  next hz=>
    obtain ⟨row,hrow,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨selector,hselector,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨expected,hexpected,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨next,hnext,success⟩ := FIv_Map.bind_success _ _ _ success
    cases Result.ok.inj success
    have rv := FIw_WordValue.mul block 16#usize row hrow
    have sv := FIw_SelectorRow.value_exact s row selector hh hlo hselector
    have root := FIy_EmptyRoot.value level expected hexpected
    have same : roots level.val=expected := by unfold roots;rw [root.1];rfl
    have dv := FIy_DigestBinding.value d out selector a poseidon2.RATE expected true
      (by rw [poseidon2.RATE];decide) hd sv.1 ha root.2 hnext
    refine ⟨dv.1,?_⟩
    intro j
    rw [dv.2 j]
    simp only [increment,if_pos (bitZero.mp hz),FIy_DigestLane.increment,sv.2,
      poseidon2.RATE,show (8#usize).val=8 from rfl,←same,rowValue,rv,blockValue,show (16#usize).val=16 from rfl]
  next hz=>
    obtain ⟨base,hbase,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨row,hrow,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨selector,hselector,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨expected,hexpected,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨next,hnext,success⟩ := FIv_Map.bind_success _ _ _ success
    cases Result.ok.inj success
    have bv := FIw_WordValue.mul block 16#usize base hbase
    have rv := FIw_WordValue.add base 12#usize row hrow
    have sv := FIw_SelectorRow.value_exact s row selector hh hlo hselector
    have slot := FIy_ArraySlot.value src.frontier level expected hexpected
    have same : frontier src level.val=expected := by unfold frontier;rw [slot];rfl
    have cb := hf expected (List.mem_of_getElem? slot)
    have dv := FIy_DigestBinding.value d out selector a 0#usize expected false (by decide) hd sv.1 ha cb hnext
    refine ⟨dv.1,?_⟩
    intro j
    rw [dv.2 j]
    simp only [increment,if_neg (fun h=>hz (bitZero.mpr h)),FIy_DigestLane.increment,sv.2,
      show (0#usize).val=0 from rfl,Nat.zero_add,←same,rowValue,rv,bv,blockValue,
      show (16#usize).val=16 from rfl,show (12#usize).val=12 from rfl]
#print axioms zero_word
#print axioms value
end AspisR1.FIy_FrontierMeaning
end
