#!/usr/bin/env python3
"""PCUF_hp.py: build PRVEq_TD_HP_P3f.lean = the P3a conditional loop refinement (PCVA_L050, hypothesis H_P) restated against the P1e emission PCQF_E002
(S009 re-run with Charon --include aspis_core::field::P, so `aspis_core.field.P : Std.U32` is a plain definition).  The fresh declarations are the
verbatim PCQF_E002 declarations (registration attributes stripped by the generator's strip_reg_attrs, namespace renamed); the proofs are the
P3a proofs with the hypothesis step replaced by the theorem P_eq."""
import sys
from pathlib import Path
sys.dont_write_bytecode=True
import PCUF_gen_equalities as G
EV=Path(__file__).resolve().parent.parent
d=next((EV/'prov-p1e-20261109/PCQF_E002_emitted/raw').glob('*'))
t=(d/'Funs.lean').read_text()
ns=d.name
blocks={b['name']:b for b in G.parse_blocks(t) if b['kind']=='decl'}
want=['aspis_core.field.P','pool_v1.pair_forest_accounts.digest_is_canonical_loop.body','pool_v1.pair_forest_accounts.digest_is_canonical_loop',
 'pool_v1.pair_forest_accounts.digest_is_canonical','pool_v1.pair_forest_accounts.first_canonical_byte','pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1']
import re
fresh=[]
for n in want:
    s=G.strip_reg_attrs(blocks[n]['text']).strip('\n')
    s=re.sub(r'\b'+re.escape(ns)+r'\.','PRVFresh_TDf.',s)
    fresh.append(s)
src_sha=__import__('hashlib').sha256(t.encode()).hexdigest()
F='AspisR1TerminalDecoder.PRVFresh_TDf'; Gt='AspisR1TerminalDecoder'
head=f"""-- PCUF_ P2f (scope item 2): discharge of the hypothesis H_P of the P3a conditional loop refinement (PCVA_L050, PRVEq_AspisR1TerminalDecoder_FunsLoop_P3.lean).
-- Fresh declarations: verbatim PCQF_E002 (P1e, overflow checks ON, aspis_core.field.P transparent) Funs.lean (sha256 {src_sha}), registration attributes stripped,
-- namespace {ns} -> {F}. There is NO hypothesis: the fresh `aspis_core.field.P` is the emitted `def P : Std.U32 := 2147483647#u32` and P_eq proves it equal to the gate P.
import Aeneas
import AspisR1TerminalDecoder.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1TerminalDecoder
namespace PRVFresh_TDf

"""
tail=f"""
end PRVFresh_TDf
end AspisR1TerminalDecoder

namespace PRVP3f

def conv : Option Bool → Bool
  | none => true
  | some b => b

/-- P_eq (replaces H_P): the fresh transparent P equals the gate P. -/
theorem P_eq : @{F}.aspis_core.field.P = @{Gt}.aspis_core.field.P := by
  unfold {F}.aspis_core.field.P {Gt}.aspis_core.field.P
  rfl
#print axioms P_eq

theorem body_refines (digest : Array {Gt}.aspis_core.field.M31 8#usize) (i : Std.Usize) :
    {Gt}.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body digest i =
    ({F}.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body digest i) >>= fun cf =>
      ok (match cf with | cont j => cont j | done o => done (conv o)) := by
  unfold {Gt}.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
    {F}.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
  rw [P_eq]
  simp only [lift, bind_tc_ok]
  by_cases h : i < Slice.len (Array.to_slice digest)
  · simp only [h, if_true, bind_tc_ok]
    rcases hm : Array.index_usize digest i with m | e | _ <;> simp [hm]
    · by_cases hp : ({Gt}.aspis_core.field.P).val ≤ m.val <;> simp [hp, conv]
  · simp only [h, if_false, bind_tc_ok, conv]
#print axioms body_refines

theorem body_cont (digest : Array {Gt}.aspis_core.field.M31 8#usize) (i j : Std.Usize)
    (h : {F}.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body digest i = ok (cont j)) :
    i.val < 8 ∧ j.val = i.val + 1 := by
  unfold {F}.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body at h
  rw [P_eq] at h
  simp only [lift, bind_tc_ok] at h
  have hlen : (Slice.len (Array.to_slice digest)).val = 8 := by
    simp [Slice.len, Array.to_slice]
  by_cases hi : i < Slice.len (Array.to_slice digest)
  · rw [if_pos hi] at h
    have hi8 : i.val < 8 := by
      have := hi; simp only [UScalar.lt_equiv] at this; omega
    refine ⟨hi8, ?_⟩
    rcases hm : Array.index_usize digest i with m | e | _
    · rw [hm] at h; simp only [bind_tc_ok] at h
      by_cases hp : m >= {Gt}.aspis_core.field.P
      · rw [if_pos hp] at h; simp at h
      · rw [if_neg hp] at h
        rcases hs : (i + 1#usize) with k | e | _
        · rw [hs] at h; simp only [bind_tc_ok] at h
          have hk := UScalar.add_equiv i 1#usize
          rw [hs] at hk
          injection h with h1; injection h1 with h2; subst h2
          simp at hk; omega
        · rw [hs] at h; simp at h
        · rw [hs] at h; simp at h
    · rw [hm] at h; simp at h
    · rw [hm] at h; simp at h
  · rw [if_neg hi] at h; simp at h

theorem loop_refines (digest : Array {Gt}.aspis_core.field.M31 8#usize) :
    ∀ (n : Nat) (i : Std.Usize), 8 - i.val ≤ n →
    {Gt}.pool_v1.pair_forest_accounts.digest_is_canonical_loop digest i =
    ({F}.pool_v1.pair_forest_accounts.digest_is_canonical_loop digest i) >>= fun o => ok (conv o) := by
  intro n
  induction n with
  | zero | succ n ih =>
    all_goals
      intro i hi
      unfold {Gt}.pool_v1.pair_forest_accounts.digest_is_canonical_loop
        {F}.pool_v1.pair_forest_accounts.digest_is_canonical_loop
      rw [Aeneas.Std.loop.eq_1, Aeneas.Std.loop.eq_1, body_refines]
      rcases hb : {F}.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body digest i with r | e | _
      · simp only [bind_tc_ok]
        cases r with
        | done o => simp
        | cont j =>
          have hc := body_cont digest i j hb
          simp only [bind_tc_ok]
          first
            | (exfalso; omega)
            | (have := ih j (by omega)
               unfold {Gt}.pool_v1.pair_forest_accounts.digest_is_canonical_loop
                 {F}.pool_v1.pair_forest_accounts.digest_is_canonical_loop at this
               exact this)
      · simp
      · simp
#print axioms loop_refines

theorem digest_is_canonical_eq (digest : Array {Gt}.aspis_core.field.M31 8#usize) :
    {F}.pool_v1.pair_forest_accounts.digest_is_canonical digest =
    {Gt}.pool_v1.pair_forest_accounts.digest_is_canonical digest := by
  unfold {F}.pool_v1.pair_forest_accounts.digest_is_canonical {Gt}.pool_v1.pair_forest_accounts.digest_is_canonical
  rw [loop_refines digest 8 0#usize (by simp)]
  rcases hl : {F}.pool_v1.pair_forest_accounts.digest_is_canonical_loop digest 0#usize with o | e | _
  · cases o <;> simp [conv]
  · simp
  · simp
#print axioms digest_is_canonical_eq

theorem first_canonical_byte_eq : @{F}.pool_v1.pair_forest_accounts.first_canonical_byte =
    @{Gt}.pool_v1.pair_forest_accounts.first_canonical_byte := by
  unfold {F}.pool_v1.pair_forest_accounts.first_canonical_byte {Gt}.pool_v1.pair_forest_accounts.first_canonical_byte
  rfl
#print axioms first_canonical_byte_eq

theorem output_lane_eq : @{F}.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 =
    @{Gt}.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 := by
  funext nullifier
  unfold {F}.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
    {Gt}.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
  rw [digest_is_canonical_eq, first_canonical_byte_eq]
#print axioms output_lane_eq
end PRVP3f
"""
Path('PRVEq_TD_HP_P3f.lean').write_text(head+'\n\n'.join(fresh)+'\n'+tail)
print('written')
