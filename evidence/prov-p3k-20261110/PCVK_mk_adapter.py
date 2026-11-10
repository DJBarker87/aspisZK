#!/usr/bin/env python3
"""PCVK_ assembler (v2) for the AdapterRw stage equalities. usage: PCVK_mk_adapter.py STAGE(1|2) OUT.lean
Fresh text: PCVK_gen_ext.py over the PCVJ emission (externals -> fields of Ext). Gate side: AdapterRwModel (git research:lean/AdapterRwModel.lean copy).
Bound relates each used Ext field to its gate counterpart (an Ops field, or a gate definition at ops) or, for the two hash fields, to the
fresh SolanaDigest.digest instance (h43). Result class: CONDITIONAL_ON_BINDING."""
import sys,json,subprocess,re
st=sys.argv[1];out=sys.argv[2]
GATE='/private/tmp/claude-501/p3k/AdapterRwModel.lean'
gate=open(GATE).read()
G='AdapterRw.'
OPS={ # original external name -> Ops field
 'Slice.Insts.CoreCmpPartialEqArray.eq':1,'Slice.Insts.CoreCmpPartialEqArray.ne':0,
 'aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1':21,
 'aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1':24,
 'r1_pool_adapter.decode_public_statement_box':47,'solana_program_error.ProgramError.Insts.CoreCloneClone.clone':35,
 'aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1':22,
 'aspis_statement.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_v1':23,
 'r1_pool_adapter.pool_program_id':45,'solana_pubkey.Pubkey.new_from_array':37,
 'aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1.nullifier':20,
 'aspis_statement.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1':17,
 'core.slice.Slice.first':9,'r1_pool_adapter.scan_proof_buffer':51,'r1_pool_adapter.reconstruct_asq8_statement':52,
 'r1_pool_adapter.decode_master_box':48,'solana_pubkey.Pubkey.to_bytes':39,
 'aspis_statement.pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_ALL_LANES_MASK':16,
 'solana_pubkey.Pubkey.Insts.CoreConvertAsRefSliceU8.as_ref':40,'solana_pubkey.Pubkey.create_program_address':38,
 'r1_pool_adapter.decode_checkpoint_box':49,'r1_pool_adapter.decode_lane_from_pool_release':50,
 'core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get':8,
 'core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut':7,
 'core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked':6,
 'core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut':5,
 'core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index':4,
 'core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut':3,
 'core.option.Option.Insts.CoreCmpPartialEqOption.eq':2,'solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq':36,
 'aspis_r1_cost_probe.verifier.candidate.tx2_authenticated':11,'error':44,'r1_pool_adapter.emit_result':53,
}
SKIP={'solana_sha256_hasher.hashv','solana_hash.Hash.to_bytes'}   # bound only through h43 (fresh SolanaDigest.digest)
MANUAL={ # polymorphic gate definitions at ops: pointwise forms
 'r1_pool_adapter.owned.require_distinct_accounts':('p','∀ (N : Std.Usize), @x.F N = @AdapterRw.r1_pool_adapter.owned.require_distinct_accounts ops N','fun {N} => @AdapterRw.r1_pool_adapter.owned.require_distinct_accounts ops N',1),
}
def gate_def(name):
    m=re.search(r'\ndef\s+'+re.escape(name)+r'(?=[\s(:])(.{0,200})',gate,re.S)
    if not m: return None
    head=m.group(1).split(':=')[0]
    return ' ops' if '(ops : Ops)' in head else ''
cfg={'1':dict(raw='../prov-p1j-20261110/PCVJ_E004_emitted/raw/PCVJ_adapter',root='r1_pool_adapter.owned.stage1_owned'),
     '2':dict(raw='../prov-p1j-20261110/PCVJ_E005_emitted/raw/PCVJ_adapter2',root='r1_pool_adapter.owned.stage2_owned')}[st]
frag='/private/tmp/claude-501/p3k/s%s.frag'%st
subprocess.check_call(['python3','PCVK_gen_ext.py',cfg['raw'],'X',cfg['root'],frag,'core.result.Result.map_err'])
fj=json.load(open(frag+'.json'));fields=fj['fields'];needx=fj['needx'];blocks=fj['blocks']
fragtxt=open(frag).read()
NS='PCVK_S%s'%st;F='AdapterRw.'+NS+'.';R=cfg['root']
poly={f for f in fields if re.search(r'^  %s : ∀'%f,fragtxt,re.M)}
bound=['structure Bound (ops : Ops) (x : Ext) : Prop where'];mk=[];prf=[];classes={}
for f,orig in fields.items():
    if orig in SKIP:
        bound_line=None;mk.append(f'    {f} := fun _ => Result.fail Error.panic');prf.append(None);classes[orig]='free (bound through h43)';continue
    if orig in MANUAL:
        t=MANUAL[orig];bound.append(f'  h_{f} : '+t[1].replace('x.F','x.'+f));mk.append(f'    {f} := {t[2]}');prf.append('fun '+' '.join(['_']*t[3])+' => rfl');classes[orig]='gate definition at ops';continue
    if orig in OPS:
        r=f'ops.op{OPS[orig]}'
        if f in poly: bound.append(f'  h_{f} : @x.{f} = @{r}');mk.append(f'    {f} := @{r}')
        else: bound.append(f'  h_{f} : x.{f} = {r}');mk.append(f'    {f} := {r}')
        prf.append('rfl');classes[orig]=f'Ops field op{OPS[orig]}';continue
    d=gate_def(orig)
    if d is None: raise SystemExit('NO GATE COUNTERPART for '+orig)
    if f in poly: raise SystemExit('poly gate def needs MANUAL: '+orig)
    r=G+orig+d
    hm=re.search(r'\ndef\s+'+re.escape(orig)+r'(?=[\s(:])(.{0,300}?):=',gate,re.S)
    if hm and ' : ' in hm.group(1) and 'Result' not in hm.group(1).split(' : ')[-1] and f not in poly and '→' not in hm.group(1).split(' : ')[-1] and '(' not in hm.group(1).replace('(ops : Ops)',''):
        r='ok ('+r+')'
    bound.append(f'  h_{f} : x.{f} = {r}');mk.append(f'    {f} := {r}');prf.append('rfl');classes[orig]='gate definition'+(' at ops' if d else '')
extras=[];extra_mk=[];extra_prf=[]
has_digest='SolanaDigest.Insts.Aspis_coreDigestDigest32.digest' in needx
if has_digest:
    extras+=[f'  h42 : ops.op42 = {F}SolanaDigest.Insts.CoreCloneClone.clone',f'  h43 : ops.op43 = {F}SolanaDigest.Insts.Aspis_coreDigestDigest32.digest x']
    extra_mk+=[f'op42 := {F}SolanaDigest.Insts.CoreCloneClone.clone','op43 := fun _ _ => Result.fail Error.panic']
hasHash='Hash : Type' in fragtxt
okeys=[f for f,o in fields.items() if o not in SKIP]
prf_all=[p for p in prf if p is not None]
if has_digest: prf_all+=['rfl','rfl']
hs=', '.join('b.h_'+f for f in fields if fields[f] not in SKIP)
# ---- x-block equalities in file order
def hdr_args(block):
    # explicit binder names after (x : Ext) in the fresh def header (up to the first ':' at depth 0)
    m=re.search(r'\ndef\s+'+re.escape(block)+r'\s*\(x : Ext\)(.*?)\n\s*:=\s*do|\ndef\s+'+re.escape(block)+r'\s*\(x : Ext\)(.*?):=',fragtxt,re.S)
    s=(m.group(1) or m.group(2))
    d=0;i=0;names=[];cur=''
    # find binder groups until depth-0 ':'
    while i<len(s):
        c=s[i]
        if c in '({[':
            d+=1
            if d==1: start=i;kind=c
        elif c in ')}]':
            d-=1
            if d==0 and kind=='(':
                grp=s[start+1:i];names+=grp.split(':')[0].split()
        elif c==':' and d==0: break
        i+=1
    return names
order=[b for b in blocks if b in needx]
cpairs=[]
for b in blocks:
    if b in needx or b in ('core.option.Option.ok_or',) or b.startswith('SolanaDigest.') or b.endswith('._eq'): continue
    d=gate_def(b)
    if d=='' :
        cpairs.append(b)
INSTS=['rf_inst_eq b','digest_inst_eq b','opt_inst_eq b','pk_inst_eq b']
eqs=[];simps=[f'data_eq b']+[f'PRVEq_S{st}_cp{i}' for i in range(len(cpairs))]
lines=[]
poly_inst={'core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice','core.option.Option.Insts.CoreCmpPartialEqOption','solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey'}
for b in order:
    if b=='r1_pool_adapter.owned.OwnedAccount.data' or b==R and False: continue
    if b in poly_inst or b.startswith('SolanaDigest.'): continue
    args=hdr_args(b)
    nm=b.replace('.','_')+'_eq'
    sset=', '.join(simps+[hs]+(INSTS if (st=='2') else [])+['hps','bind_tc_ok','hadd'] if b==R and st=='1' else simps+[hs]+(INSTS if st=='2' else []))
    if b==R and st=='1':
        body=f"""  funext {' '.join(args)}
  obtain ⟨ps, hps, hpsv⟩ := PRVEq_after_ex ops
  have h8 : (8#usize).val = 8 := by scalar_tac
  have hadd : (ps + 8#usize : Result Std.Usize) = ok (Std.Usize.wrapping_add ps 8#usize) :=
    PRVEq_usize_add_wrap ps 8#usize (by omega)
  unfold {F}{b} {G}{b}
  simp only [{sset}]
  rfl"""
    else:
        body=f"""  funext {' '.join(args)}
  unfold {F}{b} {G}{b}
  simp only [{sset}]
  delta_matchers
  rfl"""
    eqs.append(f"theorem {nm} :\n    {F}{b} x = {G}{b} ops := by\n{body}\n")
    simps.append(nm+' b')
# note: for stage 1 the single x-block root already contains the add-site proof
inst=''
cptxt=''.join(f"theorem PRVEq_S{st}_cp{i} : {F}{b} = {G}{b} := by\n  unfold {F}{b} {G}{b}\n  rfl\n\n" for i,b in enumerate(cpairs))
if st=='2':
    inst=f"""theorem clone_inst_eq :
    {F}SolanaDigest.Insts.CoreCloneClone = {G}SolanaDigest.Insts.CoreCloneClone ops := by
  unfold {F}SolanaDigest.Insts.CoreCloneClone {G}SolanaDigest.Insts.CoreCloneClone
  rw [b.h42]

theorem copy_inst_eq :
    {F}SolanaDigest.Insts.CoreMarkerCopy = {G}SolanaDigest.Insts.CoreMarkerCopy ops := by
  unfold {F}SolanaDigest.Insts.CoreMarkerCopy {G}SolanaDigest.Insts.CoreMarkerCopy
  rw [clone_inst_eq b]

theorem digest_inst_eq :
    {F}SolanaDigest.Insts.Aspis_coreDigestDigest32 x = {G}SolanaDigest.Insts.Aspis_coreDigestDigest32 ops := by
  unfold {F}SolanaDigest.Insts.Aspis_coreDigestDigest32 {G}SolanaDigest.Insts.Aspis_coreDigestDigest32
  rw [copy_inst_eq b, b.h43]

theorem pk_inst_eq :
    {F}solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey x = {G}solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops := by
  unfold {F}solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey {G}solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey
  rw [b.h_{[f for f,o in fields.items() if o=='solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq'][0] if st=='2' and any(o=='solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq' for o in fields.values()) else 'none'}]

theorem opt_inst_eq (T : Type) (i : core.cmp.PartialEq T T) :
    @{F}core.option.Option.Insts.CoreCmpPartialEqOption x T i = @{G}core.option.Option.Insts.CoreCmpPartialEqOption ops T i := by
  unfold {F}core.option.Option.Insts.CoreCmpPartialEqOption {G}core.option.Option.Insts.CoreCmpPartialEqOption
  rw [b.h_{[f for f,o in fields.items() if o=='core.option.Option.Insts.CoreCmpPartialEqOption.eq'][0] if st=='2' else 'none'}] <;> exact PRVEq_partialEq_ne_default _

theorem rf_inst_eq (T : Type) :
    @{F}core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice x T = @{G}core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ops T := by
  unfold {F}core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice {G}core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice
  rw [b.h_{[f for f,o in fields.items() if o.endswith('RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get')][0]}, b.h_{[f for f,o in fields.items() if o.endswith('SliceSlice.get_mut')][0]}, b.h_{[f for f,o in fields.items() if o.endswith('SliceSlice.get_unchecked')][0]}, b.h_{[f for f,o in fields.items() if o.endswith('SliceSlice.get_unchecked_mut')][0]}, b.h_{[f for f,o in fields.items() if o.endswith('SliceSlice.index')][0]}, b.h_{[f for f,o in fields.items() if o.endswith('SliceSlice.index_mut')][0]}]

"""
hdr=f"""-- PCVK_ AdapterRw stage{st}: fresh = gate. Fresh text: PCVJ emission (Aeneas b59d5188-extended, overflow ON, frozen 4bb3b3f), externals as fields of Ext.
-- RESULT CLASS: CONDITIONAL_ON_BINDING (see Bound). Statement: for every ops and x with Bound ops x, fresh x = gate ops.
import Aeneas
import AdapterRwModel
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AdapterRw
namespace {NS}

"""
common=f"""
end {NS}
end AdapterRw

theorem PRVEq_partialEq_ne_default {{Self Rhs : Type}} (c : Self → Rhs → Result Bool) :
    ({{ eq := c, ne := fun s o => core.cmp.PartialEq.ne.default c s o }} : core.cmp.PartialEq Self Rhs) = {{ eq := c }} := by
  have h : (fun s o => core.cmp.PartialEq.ne.default c s o) = core.cmp.PartialEq.ne._default c := by
    funext s o
    simp only [core.cmp.PartialEq.ne.default, core.cmp.PartialEq.ne._default, id]
    congr 1; funext b; cases b <;> rfl
  rw [h]; rfl

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
    ∃ ps : Std.Usize, {G}aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops = ok ps ∧ ps.val = 688 := by
  unfold {G}aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES {G}aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
  have hmax : (8#usize).val + (680#usize).val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.add_spec (x := 8#usize) (y := 680#usize) hmax)
  refine ⟨z, hz, ?_⟩
  have h8 : (8#usize).val = 8 := by scalar_tac
  have h6 : (680#usize).val = 680 := by scalar_tac
  omega

open Lean Meta Elab Tactic in
/-- unfold every matcher constant occurring in the goal (fresh and gate matchers are separate constants with equal bodies). -/
elab "delta_matchers" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let env ← getEnv
  let names := ty.foldConsts (#[] : Array Name) fun c a => if Lean.Meta.isMatcherCore env c then a.push c else a
  if names.isEmpty then return
  let ids := names.map (fun n => mkIdent n)
  evalTactic (← `(tactic| delta $ids:ident*))

{cptxt}
namespace PRVEq.AdapterStage{st}_k1
variable {{ops : AdapterRw.Ops}} {{x : {F}Ext}} (b : {F}Bound ops x)
include b

theorem data_eq :
    {F}r1_pool_adapter.owned.OwnedAccount.data x = {G}r1_pool_adapter.owned.OwnedAccount.data ops := by
  funext self
  unfold {F}r1_pool_adapter.owned.OwnedAccount.data {G}r1_pool_adapter.owned.OwnedAccount.data
  rw [b.h_solana_program_error_ProgramError_Insts_CoreCloneClone_clone]
  rfl

{inst}""" + '\n'.join(eqs) + f"""
end PRVEq.AdapterStage{st}_k1

namespace PRVEq.AdapterStage{st}_k1
open AdapterRw AdapterRw.{NS}
/-- Non-vacuity: for every ops0 there are ops (ops0 with the two digest fields set) and x with Bound ops x. -/
theorem bound_exists (ops0 : Ops) : ∃ ops : Ops, ∃ x : Ext, Bound ops x := by
  let ops : Ops := {{ ops0 with {', '.join(extra_mk)} }}
  exact ⟨ops, {{
{('    Hash := Unit'+chr(10)) if hasHash else ''}""" + '\n'.join(mk) + f"""
    }}, ⟨{', '.join(prf_all)}⟩⟩
end PRVEq.AdapterStage{st}_k1

#print axioms PRVEq_partialEq_ne_default
#print axioms PRVEq_usize_add_wrap
#print axioms PRVEq_after_ex
#print axioms PRVEq.AdapterStage{st}_k1.data_eq
""" + ''.join(f"#print axioms PRVEq.AdapterStage{st}_k1.{b.replace('.','_')}_eq\n" for b in order if not (b in poly_inst or b.startswith('SolanaDigest.') or b=='r1_pool_adapter.owned.OwnedAccount.data')) + (f"#print axioms PRVEq.AdapterStage{st}_k1.digest_inst_eq\n#print axioms PRVEq.AdapterStage{st}_k1.rf_inst_eq\n" if st=='2' else '') + f"#print axioms PRVEq.AdapterStage{st}_k1.bound_exists\n"
body=hdr+fragtxt+'\n'+'\n'.join(bound+extras)+'\n'+common
if st=='1': body=body.replace('{ ops0 with  }','ops0')
open(out,'w').write(body)
json.dump(dict(stage=st,root=R,classes=classes,x_blocks=needx,extras=['h42','h43'] if has_digest else []),open(out+'.classes.json','w'),indent=1)
print('wrote',out,len(fields),'fields',len(eqs),'eq theorems')
