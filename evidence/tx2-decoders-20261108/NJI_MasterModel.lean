import NJI_Any
import NJI_Array64
import NJI_PolicyPort
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NJI_MasterModel
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev M := NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1
abbrev F := NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
abbrev C := NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1
def capacity : U64 := 1048576#u64
def tooLarge (x : U64) : Bool := decide (x>capacity)

def mapErr {T E F O : Type} (fn : core.ops.function.FnOnce O E F)
 (r : core.result.Result T E) (f : O) : Result (core.result.Result T F) :=
 match r with
 | .Ok v => ok (.Ok v)
 | .Err e => do let e' ← fn.call_once f e;ok (.Err e')

abbrev predicate :=
 NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU64Bool (ok capacity)

theorem callback (f : C) (x : U64) : predicate.call_mut f x=ok (tooLarge x,f) := by
 unfold predicate
 simp only [NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU64Bool,
  NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU64Bool.call_mut,
  bind_tc_ok,tooLarge]

def terminal (m : M) : core.result.Result Unit F :=
 if m.has_checkpoint then
  if m.next_checkpoint_sequence=0#u64 then .Err .InvalidMasterState else .Ok ()
 else if m.next_checkpoint_sequence≠0#u64 then .Err .InvalidMasterState
 else if m.last_checkpoint_lane_sequences=Array.repeat 8#usize 0#u64 then .Ok ()
 else .Err .InvalidMasterState

def model (m : M) : Result (core.result.Result Unit F) :=
 if m.identity.pool=Array.repeat 32#usize 0#u8 then ok (.Err .ZeroRequiredBinding)
 else if m.identity.asset_mint=Array.repeat 32#usize 0#u8 then ok (.Err .ZeroRequiredBinding)
 else if m.identity.token_program=Array.repeat 32#usize 0#u8 then ok (.Err .ZeroRequiredBinding)
 else if m.identity.deployment_domain=Array.repeat 32#usize 0#u8 then ok (.Err .ZeroRequiredBinding)
 else do
  let q ← NJI_PolicyPort.validator m.verifier_policy
  match q with
  | .Err _ => ok (.Err .Policy)
  | .Ok _ => if m.last_checkpoint_lane_sequences.val.any tooLarge then ok (.Err .InvalidMasterState)
             else ok (terminal m)

def raw (m : M) :=
 NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.validate_master
  mapErr NJI_Any.any NJI_PolicyPort.validator (ok capacity) m

/-- Every zero/child-error/sequence/state rejection is retained. The callback
law and full CLOSED policy Result are applied internally on this SAME master. -/
theorem source (m : M) : raw m=model m := by
 have zero (v : Array U8 32#usize) : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 v (Array.repeat 32#usize 0#u8) = ok (decide (v=Array.repeat 32#usize 0#u8)) := NGL_ArrayEquality.eq_value v _
 obtain ⟨itOut,hany⟩:=NJI_Any.result predicate tooLarge callback
   {slice:=m.last_checkpoint_lane_sequences.to_slice,i:=0} ()
 simp only [Array.to_slice,List.drop_zero] at hany
 have hanyExact : NJI_Any.any
  (NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU64Bool (ok capacity))
  {slice:=m.last_checkpoint_lane_sequences.to_slice,i:=0} ()=
  ok (m.last_checkpoint_lane_sequences.val.any tooLarge,itOut) := hany
 unfold raw model
 simp only [NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.validate_master,
  zero,lift,bind_tc_ok,decide_eq_true_eq]
 generalize hq : NJI_PolicyPort.validator m.verifier_policy=q
 cases q with
 | fail e => simp [zero,hq]
 | div => simp [zero,hq]
 | ok q =>
  cases q with
  | Err e =>
   simp [zero,hq,mapErr,
    NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1FormatErrorPoolV1PairForestAccountErrorV1,
    NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.validate_master.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1FormatErrorPoolV1PairForestAccountErrorV1.call_once,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
  | Ok u =>
   cases u
   simp [zero,hq,mapErr,core.result.Result.Insts.CoreOpsTry.branch,core.slice.Slice.iter,
    hanyExact,Array.to_slice,NJI_Array64.ne_value,terminal]
   all_goals
    try rw [hanyExact]
    have eqzero : m.next_checkpoint_sequence=0#u64 ↔ m.next_checkpoint_sequence.val=0 := by
     constructor
     · intro h;exact congrArg UScalar.val h
     · intro h;exact UScalar.eq_of_val_eq h
    simp_all [eqzero,bind_tc_ok]
    split_ifs <;> simp_all [bind_tc_ok]

#print source
#print axioms callback
#print axioms source
end NJI_MasterModel
