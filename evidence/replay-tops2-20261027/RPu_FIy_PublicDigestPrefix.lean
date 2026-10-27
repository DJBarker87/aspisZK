import RPu_FIy_PublicDigestStep
import RPu_FIx_ArrayMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_PublicDigestPrefix
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FIy_FrontierStep (Selectors)
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings

def run (public1 : Public) (openings : Openings) (selectors : Selectors) : Result (Array NQ 8#usize) := do
  let digests := Array.repeat 8#usize field.QM31.ZERO
  let i ← 56#usize * 16#usize
  let i1 ← i + 11#usize
  let q ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i1
  let digests1 ←
    pool_v1.pair_forest_semantic_terminal.add_digest_binding digests q
      openings.z 0#usize public1.anchor false
  let i2 ← 26#usize * 16#usize
  let i3 ← i2 + 11#usize
  let q1 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i3
  let digests2 ←
    pool_v1.pair_forest_semantic_terminal.add_digest_binding digests1 q1
      openings.z 0#usize public1.nullifier false
  let digests3 ←
    match public1.recipient with
    | none => ok digests2
    | some recipient =>
      do
      let i4 ← 29#usize * 16#usize
      let i5 ← i4 + 11#usize
      let q2 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i5
      pool_v1.pair_forest_semantic_terminal.add_digest_binding digests2 q2
        openings.z 0#usize recipient false
  let i4 ← 32#usize * 16#usize
  let i5 ← i4 + 11#usize
  let q2 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i5
  let digests4 ←
    pool_v1.pair_forest_semantic_terminal.add_digest_binding digests3 q2
      openings.z 0#usize public1.change false
  ok digests4

def model (p : Public) (o : Openings) (s : Selectors) : Fin (8#usize).val → K :=
  let first := FIy_PublicDigestStep.model s o.z 907 p.anchor (fun _=>0)
  let second := FIy_PublicDigestStep.model s o.z 427 p.nullifier first
  let third := match p.recipient with
    | none=>second
    | some recipient=>FIy_PublicDigestStep.model s o.z 475 recipient second
  FIy_PublicDigestStep.model s o.z 523 p.change third

theorem value (p : Public) (o : Openings) (s : Selectors) (out : Array NQ 8#usize)
    (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low)
    (ha : ∀ x∈p.anchor.val,x.val<FIw_ScalarArithmetic.P)
    (hn : ∀ x∈p.nullifier.val,x.val<FIw_ScalarArithmetic.P)
    (hr : ∀ recipient,p.recipient=some recipient → ∀ x∈recipient.val,x.val<FIw_ScalarArithmetic.P)
    (hc : ∀ x∈p.change.val,x.val<FIw_ScalarArithmetic.P)
    (success : run p o s=ok out) :
    canonical out ∧ decoded out=model p o s := by
  unfold run at success
  obtain ⟨i,h_i,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i1,h_i1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q,h_q,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨d1,h_d1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i2,h_i2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i3,h_i3,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q1,h_q1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨d2,h_d2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨d3,h_d3,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i4,h_i4,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨i5,h_i5,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q2,h_q2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨d4,h_d4,success⟩ := FIv_Map.bind_success _ _ _ success
  have same : d4=out := Result.ok.inj success
  subst d4
  have zero : canonical (Array.repeat 8#usize field.QM31.ZERO) := by
    intro x hx
    have he : x=field.QM31.ZERO := List.eq_of_mem_replicate hx
    rw [he]
    exact FIv_NativeValue.zero.1
  have r1 := FIy_PublicDigestStep.row 56#usize 11#usize i i1 h_i h_i1
  have r2 := FIy_PublicDigestStep.row 26#usize 11#usize i2 i3 h_i2 h_i3
  have r4 := FIy_PublicDigestStep.row 32#usize 11#usize i4 i5 h_i4 h_i5
  change i1.val=907 at r1
  change i3.val=427 at r2
  change i5.val=523 at r4
  have first := FIy_PublicDigestStep.value _ d1 s o.z i1 q p.anchor zero hh hl hz ha h_q h_d1
  have second := FIy_PublicDigestStep.value d1 d2 s o.z i3 q1 p.nullifier first.1 hh hl hz hn h_q1 h_d2
  have third : canonical d3 ∧ decoded d3=(match p.recipient with
      | none=>decoded d2
      | some recipient=>FIy_PublicDigestStep.model s o.z 475 recipient (decoded d2)) := by
    cases he : p.recipient with
    | none=>
      simp only [he] at h_d3 ⊢
      have same : d2=d3 := Result.ok.inj h_d3
      subst d3
      exact ⟨second.1,rfl⟩
    | some recipient=>
      simp only [he] at h_d3 ⊢
      obtain ⟨base,hbase,h_d3⟩ := FIv_Map.bind_success _ _ _ h_d3
      obtain ⟨row,hrow,h_d3⟩ := FIv_Map.bind_success _ _ _ h_d3
      obtain ⟨selector,hselector,h_d3⟩ := FIv_Map.bind_success _ _ _ h_d3
      have rv := FIy_PublicDigestStep.row 29#usize 11#usize base row hbase hrow
      change row.val=475 at rv
      have v := FIy_PublicDigestStep.value d2 d3 s o.z row selector recipient second.1 hh hl hz (hr recipient he) hselector h_d3
      exact ⟨v.1,by rw [v.2,rv]⟩
  have last := FIy_PublicDigestStep.value d3 out s o.z i5 q2 p.change third.1 hh hl hz hc h_q2 h_d4
  refine ⟨last.1,?_⟩
  rw [last.2,r4,third.2,second.2,r2,first.2,r1,FIx_ArrayMeaning.decoded_repeat,FIv_NativeValue.zero.2]
  rfl
#print axioms value
end AspisR1.FIy_PublicDigestPrefix
end
