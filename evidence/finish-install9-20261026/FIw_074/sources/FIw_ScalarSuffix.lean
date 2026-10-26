import FIq_Native11
import FIw_ScalarArithmetic
import FIw_SelectorRow
import FIw_CoefficientTransport
import FIv_SubMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_ScalarSuffix
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIv_NativeArray (value)
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors

def run (public1 : Public) (openings : Openings) (selectors : Selectors)
    (packed5 : Array NQ 24#usize) : Result (Array NQ 24#usize) := do
  let q ← Array.index_usize openings.z 1#usize
  let q1 ← pool_v1.pair_forest_semantic_terminal.lift_m31 public1.asset_id
  let asset_difference ← field.QM31.sub q q1
  let i ← 2#usize * 16#usize
  let i1 ← i + 12#usize
  let q2 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i1
  let input_asset ← field.QM31.mul q2 asset_difference
  let i2 ← 31#usize * 16#usize
  let i3 ← i2 + 12#usize
  let q3 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i3
  let output_scalar ← field.QM31.mul q3 asset_difference
  let i4 ← 28#usize * 16#usize
  let i5 ← i4 + 12#usize
  let q4 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i5
  let private_transfer_term ← field.QM31.mul q4 asset_difference
  let withdrawal_amount_value ←
    lift (core.option.Option.unwrap_or public1.withdrawal_amount 0#u32)
  let i6 ←
    16#usize * pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK
  let i7 ← i6 + 2#usize
  let q5 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i7
  let q6 ← Array.index_usize openings.z 10#usize
  let q7 ←
    pool_v1.pair_forest_semantic_terminal.lift_m31 withdrawal_amount_value
  let q8 ← field.QM31.sub q6 q7
  let withdrawal_term ← field.QM31.mul q5 q8
  let b := core.option.Option.is_some public1.withdrawal_amount
  let scalars ←
    pool_v1.pair_forest_semantic_terminal.scalar_lanes public1.variant b
      input_asset output_scalar private_transfer_term withdrawal_term
  pool_v1.pair_forest_semantic_terminal.add_preweighted packed5 92#usize
    scalars

def selector (s : Selectors) (row : Nat) : K :=
  value s.high (row/16)*value s.low (row%16)

def model (pub : Public) (o : Openings) (s : Selectors) : List K :=
  let diff := value o.z 1-(pub.asset_id.val : K)
  FIw_CoefficientMeaning.scalar pub.variant pub.withdrawal_amount.isSome
    (selector s 44*diff) (selector s 508*diff) (selector s 460*diff)
    (selector s 1010*(value o.z 10-((pub.withdrawal_amount.getD 0#u32).val : K)))

theorem reached (pub : Public) (o : Openings) (s : Selectors)
    (out : Array NQ 24#usize)
    (success : pool_v1.pair_forest_semantic_terminal.semantic_packed pub o s=ok out) :
    ∃ packed,run pub o s packed=ok out := by
  unfold pool_v1.pair_forest_semantic_terminal.semantic_packed at success
  obtain ⟨a1,h1,r1⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨a2,h2,r2⟩ := FIv_Map.bind_success _ _ _ r1
  obtain ⟨a3,h3,r3⟩ := FIv_Map.bind_success _ _ _ r2
  obtain ⟨a4,h4,r4⟩ := FIv_Map.bind_success _ _ _ r3
  obtain ⟨a5,h5,r5⟩ := FIv_Map.bind_success _ _ _ r4
  obtain ⟨a6,h6,r6⟩ := FIv_Map.bind_success _ _ _ r5
  exact ⟨a6,r6⟩

theorem value_exact (pub : Public) (o : Openings) (s : Selectors)
    (packed out : Array NQ 24#usize)
    (hz : ∀ x∈o.z.val,Canon x) (hh : ∀ x∈s.high.val,Canon x)
    (hl : ∀ x∈s.low.val,Canon x)
    (assetBound : pub.asset_id.val<FIw_ScalarArithmetic.P)
    (amountBound : (pub.withdrawal_amount.getD 0#u32).val<FIw_ScalarArithmetic.P)
    (success : run pub o s packed=ok out) :
    ∃ scalars : Array NQ 2#usize,
      pool_v1.pair_forest_semantic_terminal.add_preweighted packed 92#usize scalars=ok out ∧
      (∀ x∈scalars.val,Canon x) ∧ scalars.val.map decode=model pub o s := by
  unfold run at success
  obtain ⟨q,h_q,r1⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q1,h_q1,r2⟩ := FIv_Map.bind_success _ _ _ r1
  obtain ⟨diff,h_diff,r3⟩ := FIv_Map.bind_success _ _ _ r2
  obtain ⟨i,h_i,r4⟩ := FIv_Map.bind_success _ _ _ r3
  obtain ⟨i1,h_i1,r5⟩ := FIv_Map.bind_success _ _ _ r4
  obtain ⟨q2,h_q2,r6⟩ := FIv_Map.bind_success _ _ _ r5
  obtain ⟨input,h_input,r7⟩ := FIv_Map.bind_success _ _ _ r6
  obtain ⟨i2,h_i2,r8⟩ := FIv_Map.bind_success _ _ _ r7
  obtain ⟨i3,h_i3,r9⟩ := FIv_Map.bind_success _ _ _ r8
  obtain ⟨q3,h_q3,r10⟩ := FIv_Map.bind_success _ _ _ r9
  obtain ⟨output,h_output,r11⟩ := FIv_Map.bind_success _ _ _ r10
  obtain ⟨i4,h_i4,r12⟩ := FIv_Map.bind_success _ _ _ r11
  obtain ⟨i5,h_i5,r13⟩ := FIv_Map.bind_success _ _ _ r12
  obtain ⟨q4,h_q4,r14⟩ := FIv_Map.bind_success _ _ _ r13
  obtain ⟨transfer,h_transfer,r15⟩ := FIv_Map.bind_success _ _ _ r14
  obtain ⟨amount,h_amount,r16⟩ := FIv_Map.bind_success _ _ _ r15
  obtain ⟨i6,h_i6,r17⟩ := FIv_Map.bind_success _ _ _ r16
  obtain ⟨i7,h_i7,r18⟩ := FIv_Map.bind_success _ _ _ r17
  obtain ⟨q5,h_q5,r19⟩ := FIv_Map.bind_success _ _ _ r18
  obtain ⟨q6,h_q6,r20⟩ := FIv_Map.bind_success _ _ _ r19
  obtain ⟨q7,h_q7,r21⟩ := FIv_Map.bind_success _ _ _ r20
  obtain ⟨q8,h_q8,r22⟩ := FIv_Map.bind_success _ _ _ r21
  obtain ⟨withdrawal,h_withdrawal,r23⟩ := FIv_Map.bind_success _ _ _ r22
  obtain ⟨scalars,h_scalars,r24⟩ := FIv_Map.bind_success _ _ _ r23
  rw [FIw_ScalarArithmetic.lift_run] at h_q1
  cases Result.ok.inj h_q1
  have amountSame : amount=pub.withdrawal_amount.getD 0#u32 := by
    have e := Result.ok.inj h_amount
    cases h : pub.withdrawal_amount <;> simpa only [h,core.option.Option.unwrap_or,lift,Option.getD] using e.symm
  rw [amountSame,FIw_ScalarArithmetic.lift_run] at h_q7
  cases Result.ok.inj h_q7
  have qcanon := FIv_NativeArray.canonical o.z _ q hz h_q
  have amountCanon := FIw_ScalarArithmetic.lift_value _ amountBound
  have assetCanon := FIw_ScalarArithmetic.lift_value _ assetBound
  have d := FIv_SubMap.qm q _ diff qcanon assetCanon.1 h_diff
  have rows2 := FIw_SelectorRow.value_exact s i1 q2 hh hl h_q2
  have rows3 := FIw_SelectorRow.value_exact s i3 q3 hh hl h_q3
  have rows4 := FIw_SelectorRow.value_exact s i5 q4 hh hl h_q4
  have rows5 := FIw_SelectorRow.value_exact s i7 q5 hh hl h_q5
  have a := FIv_NativeValue.mul q2 diff input rows2.1 d.1 h_input
  have b := FIv_NativeValue.mul q3 diff output rows3.1 d.1 h_output
  have c := FIv_NativeValue.mul q4 diff transfer rows4.1 d.1 h_transfer
  have q6canon := FIv_NativeArray.canonical o.z _ q6 hz h_q6
  have wd := FIv_SubMap.qm q6 _ q8 q6canon amountCanon.1 h_q8
  have w := FIv_NativeValue.mul q5 q8 withdrawal rows5.1 wd.1 h_withdrawal
  have sc := FIw_CoefficientMeaning.value pub.variant pub.withdrawal_amount.isSome
    input output transfer withdrawal scalars a.1 b.1 c.1 w.1 h_scalars
  refine ⟨scalars,r24,sc.1,?_⟩
  have vi1 : i1=44#usize := by
    apply UScalar.eq_of_val_eq
    scalar_tac
  have vi3 : i3=508#usize := by
    apply UScalar.eq_of_val_eq
    scalar_tac
  have vi5 : i5=460#usize := by
    apply UScalar.eq_of_val_eq
    scalar_tac
  have vi7 : i7=1010#usize := by
    unfold pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK at h_i6
    apply UScalar.eq_of_val_eq
    scalar_tac
  rw [vi1] at rows2
  rw [vi3] at rows3
  rw [vi5] at rows4
  rw [vi7] at rows5
  rw [sc.2,a.2,b.2,c.2,w.2,d.2,wd.2,rows2.2,rows3.2,rows4.2,rows5.2,
    assetCanon.2,amountCanon.2,← FIv_NativeArray.read o.z _ q h_q,
    ← FIv_NativeArray.read o.z _ q6 h_q6]
  rfl
#print axioms reached
#print axioms value_exact
end AspisR1.FIw_ScalarSuffix
end
