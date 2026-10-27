import R1Z.PV_RunJoin_BankTable19
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BankCertificate19
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_BankRow17
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

structure Certificate where
  pre : State
  absorption : State
  absorbed : Nat → State
  states : Nat → State
  before : absorbed 0 = pre
  after : states 0 = absorbed 8
  add : ∀ lane : Fin 8, ∃ sum,
    aspis_core.field.M31.add (absorbed lane.val).val[lane.val]! absorption.val[lane.val]! = ok sum ∧
    (absorbed lane.val).set (Usize.ofNatCore lane.val (by have := lane.isLt;scalar_tac)) sum = absorbed (lane.val+1)
  pair : ∀ n : Fin 11, ∃ first,
    poseidon2.evaluate_trace_round_pair (states n.val)
      (Usize.ofNatCore n.val (by have := n.isLt;scalar_tac)) = ok (some (first,states (n.val+1)))

def Certificate.row (c : Certificate) (row : Nat) : State :=
  if row = 0 then c.pre else if row < 12 then c.states row
  else if row = 12 then c.absorption else Array.repeat 16#usize aspis_core.field.M31.ZERO

theorem block (data : Nat → Nat → State) (c : Certificate) (b : Usize) (hb : b.val < 57)
    (layout : ∀ row, row < 16 → data b.val row = c.row row) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (PV_RunJoin_BankTable19.banks (PV_RunJoin_BankTable19.cells data)) b) b = ok (.Ok ()) := by
  let columns := PV_RunJoin_BankAggregate18.columns (PV_RunJoin_BankTable19.banks (PV_RunJoin_BankTable19.cells data)) b
  apply PV_RunJoin_BankBlock18.block columns b c.absorbed c.states
  · intro lane hl
    rw [show Usize.wrapping_mul b 16#usize = rowIndex b 0#usize from (by
      unfold rowIndex
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by have := umul b 16#usize (by simp;omega);simp_all;omega)]
      simp)]
    rw [PV_RunJoin_BankTable19.data_read data b 0#usize lane hb (by simp) hl]
    simp only [UScalar.ofNatCore_val_eq]
    rw [layout 0 (by decide)]
    simp only [Certificate.row,if_true,← c.before]
  · intro lane hl
    let j : Fin 8 := ⟨lane.val,hl⟩
    have hi : lane = Usize.ofNatCore j.val (by have := j.isLt;scalar_tac) := UScalar.eq_of_val_eq rfl
    obtain ⟨sum,ha,hs⟩ := c.add j
    refine ⟨c.absorption.val[lane.val]!,sum,?_,ha,?_⟩
    · change alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
        columns.val[lane.val]! (rowIndex b 12#usize) = _
      rw [PV_RunJoin_BankTable19.data_read data b 12#usize lane hb (by simp) (by omega)]
      simp only [UScalar.ofNatCore_val_eq]
      rw [layout 12 (by decide)]
      simp only [Certificate.row,show ¬(12=0) by decide,show ¬(12<12) by decide,if_false,if_true]
    · rw [← hi] at hs
      exact hs
  · exact c.after
  · intro n hn
    let j : Fin 11 := ⟨n.val,hn⟩
    have hi : n = Usize.ofNatCore j.val (by have := j.isLt;scalar_tac) := UScalar.eq_of_val_eq rfl
    have hp := c.pair j
    rw [← hi] at hp
    exact hp
  · intro n hn lane hl
    have hv : (Usize.wrapping_add n 1#usize).val = n.val+1 := by
      rw [uadd _ _ (by simp;omega)]
      rfl
    rw [PV_RunJoin_BankTable19.data_read data b _ lane hb (by rw [hv];omega) hl,
      layout _ (by rw [hv];omega),hv]
    simp only [Certificate.row,show ¬(n.val+1=0) by omega,if_false,show n.val+1<12 by omega,if_true]
  · intro n hn13 hn16 lane hl
    rw [PV_RunJoin_BankTable19.data_read data b n lane hb hn16 hl,layout _ hn16]
    simp only [Certificate.row,show ¬(n.val=0) by omega,show ¬(n.val<12) by omega,
      show ¬(n.val=12) by omega,if_false]
#print axioms block
end R1Z.PV_RunJoin_BankCertificate19
