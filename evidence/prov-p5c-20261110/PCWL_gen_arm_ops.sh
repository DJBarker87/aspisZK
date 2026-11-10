#!/bin/bash
# PCWL: AdapterRwModel items that are parametric in Ops. Fresh text = PCWL_E001 emission (original Aeneas, ON, frozen 4bb3b3f) blocks for
# readonly_meta_ok, OwnedAccount.impl.owner, require_readonly_account; the one SDK external (Pubkey eq, an axiom in the emission) is the field pk_eq of Ext, as in PCVF_ item 2.
cd "$(dirname "$0")"
python3 -B - <<'P'
import re
F=open('PCWL_E001_emitted/raw/PCWL_ar/Funs.lean').read()
blocks=re.split(r'\n(?=/--)',F)
def get(name):
    for b in blocks:
        m=re.search(r'\ndef '+re.escape(name)+r'\b',b)
        if m: return b.strip('\n')
    raise SystemExit('missing '+name)
ro=get('r1_pool_adapter.readonly_meta_ok')
ow=get('r1_pool_adapter.owned.OwnedAccount.impl.owner')
ra=get('r1_pool_adapter.owned.require_readonly_account')
inst='solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey'
ro=ro.replace('def r1_pool_adapter.readonly_meta_ok\n','def r1_pool_adapter.readonly_meta_ok (x : Ext)\n').replace(inst+' owner',  '('+inst+' x) owner')
ra=ra.replace('def r1_pool_adapter.owned.require_readonly_account\n','def r1_pool_adapter.owned.require_readonly_account (x : Ext)\n').replace('r1_pool_adapter.readonly_meta_ok p owner','(r1_pool_adapter.readonly_meta_ok x) p owner')
assert '(x : Ext)' in ro and '('+inst+' x)' in ro and '(x : Ext)' in ra and '(r1_pool_adapter.readonly_meta_ok x)' in ra
H='''-- PCWL_ AdapterRwModel, Ops-parametric items (readonly_meta_ok, require_readonly_account). Statements: fresh = gate.
-- Fresh text: PCWL_E001 emission (Charon cargo --jobs 4 identity by class receipt PCWE_E003; original Aeneas 959659a6; overflow ON; frozen 4bb3b3f), blocks readonly_meta_ok,
-- OwnedAccount.impl.owner, require_readonly_account. The emission's one external (Pubkey eq; an axiom in FunsExternal) is the field pk_eq of the parameter Ext, not an axiom.
-- RESULT CLASS: CONDITIONAL_ON_BINDING. The gate takes `ops : Ops` and uses ops.op36 as Pubkey equality; the equalities hold for every Ext whose pk_eq is bound to ops.op36.
-- Callees outside the list (core.cmp.impls.PartialEqShared.ne, trait_default, ProgramError, OwnedAccount fields) resolve by name to the gate's declarations.
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
namespace PRVFresh_ARM_w5

structure Ext where
  pk_eq : solana_pubkey.Pubkey → solana_pubkey.Pubkey → Result Bool

@[reducible]
impl_def solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (x : Ext) : core.cmp.PartialEq
  solana_pubkey.Pubkey solana_pubkey.Pubkey := {
  eq := x.pk_eq
  ne := core.cmp.PartialEq.ne.trait_default
    (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey x)
}

'''
T='''
end PRVFresh_ARM_w5
end AdapterRw

set_option maxHeartbeats 200000

namespace PRVEq.AdapterRwModel_w5
open AdapterRw

set_option maxHeartbeats 200000 in
theorem readonly_meta_ok_eq (ops : Ops) (x : PRVFresh_ARM_w5.Ext) (h : x.pk_eq = ops.op36) :
    PRVFresh_ARM_w5.r1_pool_adapter.readonly_meta_ok x = AdapterRw.r1_pool_adapter.readonly_meta_ok ops := by
  cases x; simp only at h; subst h; rfl
#print axioms readonly_meta_ok_eq

set_option maxHeartbeats 200000 in
theorem owner_eq : @PRVFresh_ARM_w5.r1_pool_adapter.owned.OwnedAccount.impl.owner = @AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.owner := by
  rfl
#print axioms owner_eq

set_option maxHeartbeats 200000 in
theorem require_readonly_account_eq (ops : Ops) (x : PRVFresh_ARM_w5.Ext) (h : x.pk_eq = ops.op36) :
    PRVFresh_ARM_w5.r1_pool_adapter.owned.require_readonly_account x = AdapterRw.r1_pool_adapter.owned.require_readonly_account ops := by
  cases x; simp only at h; subst h; rfl
#print axioms require_readonly_account_eq

end PRVEq.AdapterRwModel_w5
'''
open('PRVEq_AdapterRwModel_w5.lean','w').write(H+ro+'\n\n'+ow+'\n\n'+ra+'\n'+T)
P
