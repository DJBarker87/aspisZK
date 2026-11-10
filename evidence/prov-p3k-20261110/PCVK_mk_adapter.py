#!/usr/bin/env python3
"""PCVK_ assembler for the AdapterRw stage equalities. usage: PCVK_mk_adapter.py STAGE(1|2) OUT.lean
Inputs: fragment from PCVK_gen_ext.py (fresh text with externals as fields of Ext) and the hand Bound table below."""
import sys,json,subprocess,re
st=sys.argv[1];out=sys.argv[2]
G='AdapterRw.'
A='aspis_statement.pool_v1.'
# original external name -> (kind, rhs).  kind 'c': monomorphic, hypothesis  x.f = rhs.  'p': polymorphic, hand text.
TABLE={
 'Slice.Insts.CoreCmpPartialEqArray.eq':('p','∀ (T U : Type) (N : Std.Usize) (i : core.cmp.PartialEq T U), @x.F T U N i = @ops.op1 T U N i','@ops.op1',4),
 'Slice.Insts.CoreCmpPartialEqArray.ne':('p','∀ (T U : Type) (N : Std.Usize) (i : core.cmp.PartialEq T U), @x.F T U N i = @ops.op0 T U N i','@ops.op0',4),
 'r1_pool_adapter.owned.require_distinct_accounts':('p','∀ (N : Std.Usize), @x.F N = @'+G+'r1_pool_adapter.owned.require_distinct_accounts ops N','fun {N} => @'+G+'r1_pool_adapter.owned.require_distinct_accounts ops N',1),
 'aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1':('c','ops.op21'),
 'aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1':('c','ops.op24'),
 'r1_pool_adapter.decode_public_statement_box':('c','ops.op47'),
 'solana_program_error.ProgramError.Insts.CoreCloneClone.clone':('c','ops.op35'),
 'aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common':('c',G+'aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common'),
 'aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public':('c',G+'aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public'),
 'aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES':('c',G+'aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops'),
 'r1_pool_adapter.owned.require_verifier_checkpoint':('c',G+'r1_pool_adapter.owned.require_verifier_checkpoint ops'),
 'r1_pool_adapter.owned.require_readonly_buffer':('c',G+'r1_pool_adapter.owned.require_readonly_buffer'),
 'r1_pool_adapter.owned.require_zero':('c',G+'r1_pool_adapter.owned.require_zero'),
 'aspis_r1_cost_probe.transport.Variant.tag':('c',G+'aspis_r1_cost_probe.transport.Variant.tag'),
 'aspis_r1_cost_probe.verifier.PROOF_BYTES':('c',G+'aspis_r1_cost_probe.verifier.PROOF_BYTES'),
 'first_decoded':('c',G+'first_decoded ops'),
}

cfg={'1':dict(raw='../prov-p1j-20261110/PCVJ_E004_emitted/raw/PCVJ_adapter',root='r1_pool_adapter.owned.stage1_owned'),
     '2':dict(raw='../prov-p1j-20261110/PCVJ_E005_emitted/raw/PCVJ_adapter2',root='r1_pool_adapter.owned.stage2_owned')}[st]
frag='/private/tmp/claude-501/p3k/s%s.frag'%st
subprocess.check_call(['python3','PCVK_gen_ext.py',cfg['raw'],'X',cfg['root'],frag,'core.result.Result.map_err'])
fj=json.load(open(frag+'.json'));fields=fj['fields']
fragtxt=open(frag).read()
NS='PCVK_S%s'%st;F='AdapterRw.'+NS+'.';Gp='AdapterRw.';R=cfg['root']
hdr=f"""-- PCVK_ AdapterRw stage{st}: fresh = gate. Fresh text: PCVJ emission (Aeneas b59d5188-extended, overflow ON, frozen 4bb3b3f), externals as fields of Ext.
-- RESULT CLASS: CONDITIONAL_ON_BINDING (see Bound). Statement: for every ops and x with Bound ops x, fresh x = gate ops.
import Aeneas
import AdapterRwModel
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AdapterRw
namespace {NS}

"""
bound=['structure Bound (ops : Ops) (x : Ext) : Prop where'];mk=[];prf=[]
for f,orig in fields.items():
    if orig not in TABLE: raise SystemExit('NO TABLE ENTRY '+orig)
    t=TABLE[orig]
    if t[0]=='c':
        bound.append(f'  h_{f} : x.{f} = {t[1]}'); mk.append(f'    {f} := {t[1]}'); prf.append('rfl')
    else:
        bound.append(f'  h_{f} : '+t[1].replace('x.F','x.'+f)); mk.append(f'    {f} := {t[2]}'); prf.append('fun '+' '.join(['_']*t[3])+' => rfl')
hs=', '.join('b.h_'+f for f in fields)
proofs=f"""
end {NS}
end AdapterRw

theorem PRVEq_usize_add_wrap (a b : Std.Usize) (h : a.val + b.val < 4294967296) :
    (a + b : Result Std.Usize) = ok (Std.Usize.wrapping_add a b) := by
  have hmax : a.val + b.val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.add_spec (x := a) (y := b) hmax)
  rw [hz]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hv, Std.Usize.wrapping_add_val_eq]
  have h2 : a.val + b.val < UScalar.size UScalarTy.Usize := by
    rw [Std.Usize.max_def] at hmax
    rw [UScalar.size_UScalarTyUsize, Std.Usize.size_def]
    have := Nat.one_le_two_pow (n := Std.Usize.numBits)
    omega
  exact (Nat.mod_eq_of_lt h2).symm

theorem PRVEq_after_ex (ops : AdapterRw.Ops) :
    ∃ ps : Std.Usize, {Gp}aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops = ok ps ∧ ps.val = 688 := by
  unfold {Gp}aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES {Gp}aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
  have hmax : (8#usize).val + (680#usize).val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.add_spec (x := 8#usize) (y := 680#usize) hmax)
  refine ⟨z, hz, ?_⟩
  have h8 : (8#usize).val = 8 := by scalar_tac
  have h6 : (680#usize).val = 680 := by scalar_tac
  omega

namespace PRVEq.AdapterStage{st}_k1
variable {{ops : AdapterRw.Ops}} {{x : {F}Ext}} (b : {F}Bound ops x)
include b

theorem data_eq :
    {F}r1_pool_adapter.owned.OwnedAccount.data x = {Gp}r1_pool_adapter.owned.OwnedAccount.data ops := by
  funext self
  unfold {F}r1_pool_adapter.owned.OwnedAccount.data {Gp}r1_pool_adapter.owned.OwnedAccount.data
  rw [b.h_solana_program_error_ProgramError_Insts_CoreCloneClone_clone]
  rfl

theorem stage_eq :
    {F}{R} x = {Gp}{R} ops := by
  funext program_id accounts data
  obtain ⟨ps, hps, hpsv⟩ := PRVEq_after_ex ops
  have h8 : (8#usize).val = 8 := by scalar_tac
  have hadd : (ps + 8#usize : Result Std.Usize) = ok (Std.Usize.wrapping_add ps 8#usize) :=
    PRVEq_usize_add_wrap ps 8#usize (by omega)
  unfold {F}{R} {Gp}{R}
  simp only [data_eq b, {hs}, hps, bind_tc_ok, hadd]
  rfl

end PRVEq.AdapterStage{st}_k1

namespace PRVEq.AdapterStage{st}_k1
open AdapterRw AdapterRw.{NS}
/-- Non-vacuity: for every ops there is an Ext satisfying Bound (each field is the gate counterpart). -/
theorem bound_exists (ops : Ops) : ∃ x : Ext, Bound ops x :=
  ⟨{{
""" + '\n'.join(mk) + f"""
    }}, ⟨{', '.join(prf)}⟩⟩
end PRVEq.AdapterStage{st}_k1

#print axioms PRVEq_usize_add_wrap
#print axioms PRVEq_after_ex
#print axioms PRVEq.AdapterStage{st}_k1.data_eq
#print axioms PRVEq.AdapterStage{st}_k1.stage_eq
#print axioms PRVEq.AdapterStage{st}_k1.bound_exists
"""
open(out,'w').write(hdr+fragtxt+'\n'+'\n'.join(bound)+'\n'+proofs)
json.dump(dict(fields=fields,mk=mk),open(out+'.mk.json','w'),indent=1)
print('wrote',out,len(fields),'fields')
