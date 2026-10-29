"""Symbolic empty-frontier witness: read table rows without evaluating words."""
from pathlib import Path
import sys
p=Path('evidence/pv-b3p6-20261028/lean/PV_B3P_EmptyFrontierSuccess227.lean')
s='''import PV_B3P_CarrySuccess227
import PV_B3P_ArraySelfSuccess227
import PV_B3P_ArrayEight226
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
abbrev Digest227 := Array U32 8#usize
abbrev Frontier227 := Array Digest227 20#usize

def empty_cell (i : Nat) (hi : i<21) : Digest227 :=
  reference_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1.val[i]'(by
    have h := reference_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1.property
    change _ = 21 at h
    omega)

def empty_frontier : Frontier227 :=
  ⟨reference_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1.val.take 20,by
    have h := reference_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1.property
    change _ = 21 at h
    simp only [List.length_take]
    change min 20 _ = 20
    omega⟩

theorem empty_root_result (level : Usize) (hi : level.val<20) :
    reference_terminal.empty_root level = .ok (empty_cell level.val (by omega)) := by
  let root := empty_cell level.val (by omega)
  have hroot : Array.index_usize reference_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1 level = .ok root :=
    PV_B3P_SelectIndex227.index_value _ level (by change level.val<21; omega)
  unfold reference_terminal.empty_root
  rw [hroot]
  simp only [bind_tc_ok]
'''
for i in range(8):
 s+=f'''  rw [PV_B3P_SelectIndex227.index_value root {i}#usize (by change {i}<8; omega)]
  simp only [bind_tc_ok]
'''
s+='''  apply congrArg Result.ok
  apply Subtype.ext
  change PV_B3P_ArrayEight226.readEight root = root.val
  exact PV_B3P_ArrayEight226.values root

theorem empty_frontier_result (level : Usize) (hi : level.val<20) :
    reference_terminal.digest227 empty_frontier level = .ok (empty_cell level.val (by omega)) := by
  unfold reference_terminal.digest227
  rw [PV_B3P_SelectIndex227.index_value empty_frontier level (by change level.val<20; omega)]
  apply congrArg Result.ok
  simp only [empty_frontier,empty_cell,List.getElem_take]

/-- All expected frontier branches have the same symbolic row. -/
theorem empty_transition_step (index : U64) (carry level : Usize) (hi : level.val<20) :
    reference_terminal.validate_transition_loop.body index empty_frontier empty_frontier carry level =
      .ok (.cont (Usize.wrapping_add level 1#usize)) := by
  have hb : level<20#usize := by scalar_tac
  have he := empty_root_result level hi
  have hd := empty_frontier_result level hi
  have hn := digest_ne_self (empty_cell level.val (by omega))
  simp only [reference_terminal.validate_transition_loop.body,hb,↓reduceIte,
    lift,bind_tc_ok,he,hd,ite_self,hn,Bool.false_eq_true]

/-- Twenty-level successful validation loop, by an invariant on the remaining
levels. No concrete empty-root numeral or frontier word is reduced. -/
theorem empty_transition_loop (index : U64) (carry : Usize) (n : Nat) (level : Usize)
    (hi : level.val+n=20) :
    reference_terminal.validate_transition_loop index empty_frontier empty_frontier carry level = .ok none := by
  induction n generalizing level with
  | zero =>
    have hb : ¬level<20#usize := by scalar_tac
    unfold reference_terminal.validate_transition_loop
    rw [loop.eq_1]
    simp only [reference_terminal.validate_transition_loop.body,hb,↓reduceIte]
  | succ n ih =>
    have hb : level.val<20 := by omega
    have hn : (Usize.wrapping_add level 1#usize).val = level.val+1 :=
      PV_B3P_Offset226V3.add_value level 1#usize (by
        have hsize := usize_1024_size
        change level.val+1 < _
        omega)
    have ht := ih (Usize.wrapping_add level 1#usize) (by omega)
    unfold reference_terminal.validate_transition_loop at ht ⊢
    rw [loop.eq_1,empty_transition_step index carry level hb]
    exact ht

#print axioms empty_root_result
#print axioms empty_frontier_result
#print axioms empty_transition_step
#print axioms empty_transition_loop
end PV_B3P_Success227
'''
if '--check'in sys.argv:assert p.read_text()==s
else:p.write_text(s)
