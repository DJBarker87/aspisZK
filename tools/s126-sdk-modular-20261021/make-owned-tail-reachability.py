#!/usr/bin/env python3
from pathlib import Path
R=Path(__file__).resolve().parents[2];O=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021/S2OwnedStage1ReachabilityV1.lean'
s='''import S2OwnedStage1ModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.Reachability
open AspisS2OwnedStage1
abbrev Statement := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Public := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem first_decoded_success (ops : Ops) (pub : Public) (bytes proof : Slice U8)
    (k : Usize) (checkpoint : alloc.vec.Vec U8)
    (h : first_decoded ops pub bytes proof k=ok (.Ok checkpoint)) :
    ops.op2 (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      pub bytes proof k () none=ok (.Ok checkpoint) := by
  unfold first_decoded observer at h
  simp only [bind_tc_ok] at h
  obtain ⟨r,hr,h⟩ := bind_success _ _ _ h
  cases r with
  | Ok value =>
    simp only [core.result.Result.map_err] at h
    cases h
    exact hr
  | Err e =>
    change (do let mapped ← ops.op10 e; ok (core.result.Result.Err mapped)) = ok (.Ok checkpoint) at h
    obtain ⟨mapped,hmapped,h⟩ := bind_success _ _ _ h
    cases h

/-- One enclosing emitted owned-tail success supplies its own snapshot,
decoded statement, same semantic-public projection and release-None verifier
execution. Decoder/statement/child success are conclusions, not premises.
SDK IO and child interpretations remain named Ops fields at this scope. -/
theorem tail_success (ops : Ops) (checkpointIn data checkpointOut : Slice U8)
    (h : owned_stage1_tail ops checkpointIn data=ok (.Ok (),checkpointOut)) :
    ∃ (publicData proofData : alloc.vec.Vec U8) (statement : Statement)
      (pub : Public) (selectedProof : Slice U8)
      (proofLength proofStart proofEnd : Usize) (checkedEnd : Option Usize) (splitByte : U8) (k : Usize)
      (checkpoint : alloc.vec.Vec U8),
      ops.op11=ok (.Ok publicData) ∧
      decode_public_statement_box ops (alloc.vec.Vec.deref publicData)=ok (.Ok statement) ∧
      ops.op12=ok (.Ok proofData) ∧
      ops.op3=ok proofLength ∧
      ops.op6=ok proofStart ∧
      lift (Usize.checked_add proofStart proofLength)=ok checkedEnd ∧
      ops.op1 checkedEnd solana_program_error.ProgramError.InvalidAccountData=ok (.Ok proofEnd) ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proofData {start:=proofStart,«end»:=proofEnd}=ok selectedProof ∧
      Slice.index_usize data 1#usize=ok splitByte ∧
      lift (UScalar.cast .Usize splitByte)=ok k ∧
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement=ok pub ∧
      first_decoded ops pub (alloc.vec.Vec.deref publicData) selectedProof k=ok (.Ok checkpoint) ∧
      ops.op2 (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        pub (alloc.vec.Vec.deref publicData) selectedProof k () none=ok (.Ok checkpoint) ∧
      core.slice.Slice.copy_from_slice core.marker.CopyU8 checkpointIn
        (alloc.vec.Vec.deref checkpoint)=ok checkpointOut := by
  unfold owned_stage1_tail at h
'''
norm=['core.result.Result.Insts.CoreOpsTry.branch','core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual','core.convert.FromSame.from','bind_tc_ok']
def bind(n,lev):
 global s
 s+='  '*lev+'obtain ⟨'+n+',h'+n+',h⟩ := bind_success _ _ _ h\n'
def rust(n,lev,extra=[]):
 global s
 bind(n,lev)
 s+='  '*lev+'cases '+n+' with\n'+'  '*lev+'| Err e =>\n'
 s+='  '*(lev+1)+'simp only ['+', '.join(extra+norm)+'] at h\n'+'  '*(lev+1)+'cases h\n'
 s+='  '*lev+'| Ok '+n+'Value =>\n'
 s+='  '*(lev+1)+'simp only ['+', '.join(extra+norm)+'] at h\n'
 return lev+1
lev=rust('publicRead',1)
lev=rust('decoded',lev)
closure='owned_stage1_tail.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError'
lev=rust('validated',lev,['core.result.Result.map_err',closure,closure+'.call_once'])
s+='  '*lev+'cases validatedValue\n'
bind('common',lev)
closure='owned_stage1_tail.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError'
lev=rust('encoded',lev,['core.result.Result.map_err',closure,closure+'.call_once'])
lev=rust('proofRead',lev)
for name in ['proofLength','proofStart','checkedEnd']:bind(name,lev)
lev=rust('proofEnd',lev)
def reject_if(lev):
 global s
 s+='  '*lev+'split at h\n'+'  '*lev+'· cases h\n'+'  '*lev+'·\n'
 return lev+1
lev=reject_if(lev)
for name in ['frame','different']:bind(name,lev)
lev=reject_if(lev)
for name in ['tagOffset','storedTag','tag']:bind(name,lev)
lev=reject_if(lev)
for name in ['pub','selected','splitByte','k']:bind(name,lev)
lev=rust('child',lev)
lev=reject_if(lev)
bind('copied',lev)
s+='  '*lev+'cases h\n'
s+='  '*lev+'exact ⟨publicReadValue,proofReadValue,decodedValue,pub,selected,proofLength,proofStart,proofEndValue,checkedEnd,splitByte,k,childValue,\n'
s+='  '*(lev+1)+'hpublicRead,hdecoded,hproofRead,hproofLength,hproofStart,hcheckedEnd,hproofEnd,hselected,hsplitByte,hk,hpub,hchild,\n'
s+='  '*(lev+1)+'first_decoded_success ops pub _ _ k childValue hchild,hcopied⟩\n'
s+='''
#print axioms first_decoded_success
#print axioms tail_success
end AspisS2OwnedStage1.Reachability
'''
O.write_text(s)
