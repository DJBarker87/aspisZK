import FIy_PublicDigestPrefix
import FIy_Carry
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_PublicDigestSuffix
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FIy_FrontierStep (Selectors Snapshot)
open FIy_PublicDigestPrefix (Public Openings)

def run (public1 : Public) (openings : Openings) (selectors : Selectors)
    (digests5 : Array NQ 8#usize) (source : Snapshot) : Result (Array NQ 8#usize) := do
  let i6 ← 53#usize * 16#usize
  let i7 ← i6 + 11#usize
  let q3 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i7
  let digests6 ←
    pool_v1.pair_forest_semantic_terminal.add_digest_binding digests5 q3
      openings.z 0#usize public1.transition.candidate_afterstate.next_root
      false
  let carry ←
    pool_v1.pair_forest_semantic_terminal.bounded_append_carry
      source.next_pair_index
  if carry < 20#usize
  then
    let i8 ← 33#usize + carry
    let i9 ← i8 * 16#usize
    let i10 ← i9 + 11#usize
    let q4 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i10
    let a ←
      Array.index_usize public1.transition.candidate_afterstate.next_frontier
        carry
    pool_v1.pair_forest_semantic_terminal.add_digest_binding digests6 q4
      openings.z 0#usize a false
  else ok digests6

def next (p : Public) (carry : Nat) : Array U32 8#usize :=
  (p.transition.candidate_afterstate.next_frontier.val[carry]?).getD (Array.repeat 8#usize 0#u32)
def model (p : Public) (o : Openings) (s : Selectors) (src : Snapshot)
    (old : Fin (8#usize).val → K) : Fin (8#usize).val → K :=
  let first := FIy_PublicDigestStep.model s o.z 859 p.transition.candidate_afterstate.next_root old
  let carry := R0P.digestCarry src.next_pair_index.val
  if carry<20 then FIy_PublicDigestStep.model s o.z ((33+carry)*16+11) (next p carry) first else first

theorem value (p : Public) (o : Openings) (s : Selectors) (initial out : Array NQ 8#usize) (src : Snapshot)
    (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low) (hi : canonical initial)
    (hn : ∀ x∈p.transition.candidate_afterstate.next_root.val,x.val<FIw_ScalarArithmetic.P)
    (hf : ∀ row∈p.transition.candidate_afterstate.next_frontier.val,∀ x∈row.val,x.val<FIw_ScalarArithmetic.P)
    (success : run p o s initial src=ok out) :
    canonical out ∧ decoded out=model p o s src (decoded initial) := by
  unfold run at success
  obtain ⟨i6,h_i6,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i7,h_i7,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q3,h_q3,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨d6,h_d6,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨carry,h_carry,success⟩ := FIv_Map.bind_success _ _ _ success
  have rv := FIy_PublicDigestStep.row 53#usize 11#usize i6 i7 h_i6 h_i7
  change i7.val=859 at rv
  have first := FIy_PublicDigestStep.value initial d6 s o.z i7 q3 p.transition.candidate_afterstate.next_root
    hi hh hl hz hn h_q3 h_d6
  have cv := FIy_Carry.caller src.next_pair_index carry h_carry
  split at success
  next hc=>
    obtain ⟨block,hblock,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨base,hbase,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨row,hrow,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨selector,hselector,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨expected,hexpected,success⟩ := FIv_Map.bind_success _ _ _ success
    have bv := FIw_WordValue.add 33#usize carry block hblock
    change block.val=33+carry.val at bv
    have finalRow := FIy_PublicDigestStep.row block 11#usize base row hbase hrow
    have slot := FIy_ArraySlot.value p.transition.candidate_afterstate.next_frontier carry expected hexpected
    have same : next p carry.val=expected := by unfold next;rw [slot];rfl
    have last := FIy_PublicDigestStep.value d6 out s o.z row selector expected first.1 hh hl hz
      (hf expected (List.mem_of_getElem? slot)) hselector success
    refine ⟨last.1,?_⟩
    rw [last.2,first.2,rv,finalRow,bv]
    have h : R0P.digestCarry src.next_pair_index.val<20 := by rw [←cv.1];exact hc
    simp only [model,if_pos h,←cv.1,←same,show (11#usize).val=11 from rfl]
  next hc=>
    have eq : d6=out := Result.ok.inj success
    subst d6
    refine ⟨first.1,?_⟩
    rw [first.2,rv]
    have h : ¬R0P.digestCarry src.next_pair_index.val<20 := by rw [←cv.1];exact hc
    simp only [model,if_neg h]
#print axioms value
end AspisR1.FIy_PublicDigestSuffix
end
