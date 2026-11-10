#!/usr/bin/env python3
"""PCVK_ assembler for AspisR1CurrentCaller.verifier.candidate.{prepare,tx1}: fresh (PCVJ_E002 emission, overflow ON) = gate (CurrentCompactCallerModelV1, 21-field Ops).
usage: PCVK_mk_caller.py OUT.lean.   Result class: CONDITIONAL_ON_BINDING (callees and the six constant/error fields of Ops are bound by hypotheses)."""
import sys,json,subprocess,re
out=sys.argv[1]
gate=open('/private/tmp/claude-501/p3k/CCC.lean').read()
G='AspisR1CurrentCaller.'
OPS={'verifier.candidate.parse_shape':3,'verifier.candidate.canonical_scan':4,'verifier.candidate.wide_view':5,'verifier.candidate.batch_merkle':6,
 'verifier.candidate.query_loop':7,'verifier.Prepared.new':8,'r1_semantic.verify_observed':9,'compact.expand_semantic':10,'compact.expand_values':11,
 'verifier.checkpoint':16,'verifier.BatchedWeights.finish':17,'verifier.BatchedWeights.new':18,'verifier.QueryGeometry.for_range':19,
 'verifier.Accumulator.new':20,'aspis_core.r0.heap.filled':1}
def gate_def(name):
    m=re.search(r'(?:\n|\]\s)def\s+'+re.escape(name)+r'(?=[\s(:])(.{0,200})',gate,re.S)
    if not m: return None
    return ' ops' if '(ops : Ops)' in m.group(1).split(':=')[0] else ''
raw='../prov-p1j-20261110/PCVJ_E002_emitted/raw/PCVJ_top'
frag='/private/tmp/claude-501/p3k/c.frag'
subprocess.check_call(['python3','PCVK_gen_ext.py',raw,'X','verifier.candidate.prepare,verifier.candidate.tx1',frag,'core.result.Result.map_err'])
fj=json.load(open(frag+'.json'));fields=fj['fields'];needx=fj['needx'];blocks=fj['blocks']
fragtxt=open(frag).read()
NS='PCVK_C';F=G+NS+'.'
poly={f for f in fields if re.search(r'^  %s : ∀'%f,fragtxt,re.M)}
bound=['structure Bound (ops : Ops) (x : Ext) : Prop where'];mk=[];prf=[];classes={}
for f,orig in fields.items():
    if orig in OPS:
        r=f'ops.op{OPS[orig]}';classes[orig]=f'Ops field op{OPS[orig]}'
    else:
        d=gate_def(orig)
        if d is None: raise SystemExit('NO GATE COUNTERPART '+orig)
        if f in poly: raise SystemExit('poly gate def '+orig)
        r=G+orig+d;classes[orig]='gate definition'+(' at ops' if d else '')
    if f in poly: bound.append(f'  h_{f} : @x.{f} = @{r}');mk.append(f'    {f} := @{r}')
    else: bound.append(f'  h_{f} : x.{f} = {r}');mk.append(f'    {f} := {r}')
    prf.append('rfl')
# constant / error-conversion bindings of Ops fields to fresh definitions (CONDITIONAL_ON_BINDING)
EX=[('h_op2',f'ops.op2 = {F}verifier.Error.Insts.CoreConvertFromCodecError.from','op2'),
    ('h_op12',f'ops.op12 = ok {F}compact.OFF_SEMANTIC','op12'),
    ('h_op13',f'ops.op13 = {F}compact.COMPACT_SEMANTIC','op13'),
    ('h_op14',f'ops.op14 = {F}compact.COMPACT_Y1','op14'),
    ('h_op15',f'ops.op15 = {F}compact.LOGICAL_SEMANTIC','op15'),
    ('h_op21',f'ops.op21 = {F}compact.OFF_ROUND0','op21')]
extras=[f'  {n} : {s}' for n,s,_ in EX]
ops_over=[f"{o} := {s.split(' = ',1)[1]}" for n,s,o in EX]
prf_all=prf+['rfl']*len(EX)
hs=', '.join('b.h_'+f for f in fields)
hx=', '.join('b.'+n for n,_,_ in EX)
def hdr_info(block,hasx=True):
    xs=r'\s*\(x : Ext\)' if hasx else ''
    m=re.search(r'(?:\n|\]\s)def\s+'+re.escape(block)+xs+r'(.*?)\n\s*:=\s*do|(?:\n|\]\s)def\s+'+re.escape(block)+xs+r'(.*?):=',fragtxt,re.S)
    s=(m.group(1) or m.group(2));d=0;i=0;names=[];imp=[]
    while i<len(s):
        c=s[i]
        if c in '({[':
            d+=1
            if d==1: start=i;kind=c
        elif c in ')}]':
            d-=1
            if d==0 and kind=='(': names+=s[start+1:i].split(':')[0].split()
            if d==0 and kind=='{': imp.append(s[start+1:i])
        elif c==':' and d==0: break
        i+=1
    return names,imp
# cps: fresh blocks without x and gate def without ops
cpairs=[]
for b in blocks:
    if b in needx or b in ('core.option.Option.ok_or',): continue
    if gate_def(b)=='': cpairs.append(b)
def cp_text(i,b):
    names,imp=hdr_info(b,False)
    binders=' '.join(f'({g})' for g in imp);ap=' '.join(g.split(':')[0].strip() for g in imp)
    return f"theorem PRVEq_C_cp{i} {binders} : @{F}{b} {ap} = @{G}{b} {ap} := by\n  unfold {F}{b} {G}{b}\n  rfl\n\n"
cptxt=''.join(cp_text(i,b) for i,b in enumerate(cpairs))
cpn=[f'PRVEq_C_cp{i}' for i in range(len(cpairs))]
# constants with ops in gate: derived equalities (names fixed)
cons=f"""theorem c_off_semantic : {G}compact.OFF_SEMANTIC ops = ok {F}compact.OFF_SEMANTIC := by
  unfold {G}compact.OFF_SEMANTIC
  exact b.h_op12

theorem c_off_y1 : {G}compact.OFF_Y1 ops = {F}compact.OFF_Y1 := by
  unfold {G}compact.OFF_Y1 {F}compact.OFF_Y1
  simp only [c_off_semantic b, b.h_op13, bind_tc_ok]

theorem c_off_inactive : {G}compact.OFF_INACTIVE ops = {F}compact.OFF_INACTIVE := by
  unfold {G}compact.OFF_INACTIVE {F}compact.OFF_INACTIVE
  simp only [c_off_y1 b, b.h_op14]

theorem c_logical_semantic : {G}compact.LOGICAL_SEMANTIC ops = {F}compact.LOGICAL_SEMANTIC := by
  unfold {G}compact.LOGICAL_SEMANTIC
  exact b.h_op15

theorem c_off_folded_root : {G}compact.OFF_FOLDED_ROOT ops = {F}compact.OFF_FOLDED_ROOT := by
  unfold {G}compact.OFF_FOLDED_ROOT {F}compact.OFF_FOLDED_ROOT
  simp only [b.h_op21]

theorem c_off_round1 : {G}compact.OFF_ROUND1 ops = {F}compact.OFF_ROUND1 := by
  unfold {G}compact.OFF_ROUND1 {F}compact.OFF_ROUND1
  simp only [c_off_folded_root b]

theorem c_error_inst : {G}verifier.Error.Insts.CoreConvertFromCodecError ops = {F}verifier.Error.Insts.CoreConvertFromCodecError := by
  unfold {G}verifier.Error.Insts.CoreConvertFromCodecError {F}verifier.Error.Insts.CoreConvertFromCodecError
  rw [b.h_op2]

"""
cs=['c_off_semantic b','c_off_y1 b','c_off_inactive b','c_logical_semantic b','c_off_folded_root b','c_off_round1 b','c_error_inst b']
eqs=[];simps=cpn+cs
for blk in [b for b in blocks if b in needx]:
    names,imp=hdr_info(blk)
    nm=blk.replace('.','_')+'_eq'
    impnames=[g.split(':')[0].strip() for g in imp]
    binders=' '.join(f'({g})' for g in imp)
    app_f='@'+F+blk+' x '+' '.join(impnames);app_g='@'+G+blk+' ops '+' '.join(impnames)
    sset=', '.join(simps+[hs,'bind_tc_ok'])
    stmt=f"theorem {nm} {binders} :\n    {app_f} = {app_g} := by"
    body=f"""
  funext {' '.join(names)}
  unfold {F}{blk} {G}{blk}
  simp only [{sset}]
  delta_matchers
  rfl"""
    eqs.append(stmt+body+'\n')
    if imp: simps=simps+[f'{nm} b']
    else: simps=simps+[f'{nm} b']
hdr=f"""-- PCVK_ CurrentCompactCaller prepare/tx1: fresh = gate. Fresh text: PCVJ_E002 emission (Aeneas b59d5188-extended, overflow ON, frozen 4bb3b3f), externals as fields of Ext.
-- RESULT CLASS: CONDITIONAL_ON_BINDING (see Bound). Statement: for every ops and x with Bound ops x, fresh x = gate ops.
import Aeneas
import CurrentCompactCallerModelV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1CurrentCaller
namespace {NS}

"""
tail=f"""
end {NS}
end AspisR1CurrentCaller

{cptxt}
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

namespace PRVEq.CallerPrepTx1_k1
variable {{ops : AspisR1CurrentCaller.Ops}} {{x : {F}Ext}} (b : {F}Bound ops x)
include b

{cons}
""" + '\n'.join(eqs) + f"""
end PRVEq.CallerPrepTx1_k1

namespace PRVEq.CallerPrepTx1_k1
open AspisR1CurrentCaller AspisR1CurrentCaller.{NS}
/-- Non-vacuity: for every ops0 there are ops (ops0 with the six constant/error fields set) and x with Bound ops x. -/
theorem bound_exists (ops0 : Ops) : ∃ ops : Ops, ∃ x : Ext, Bound ops x := by
  let ops : Ops := {{ ops0 with {', '.join(ops_over)} }}
  exact ⟨ops, {{
""" + '\n'.join(mk) + f"""
    }}, ⟨{', '.join(prf_all)}⟩⟩
end PRVEq.CallerPrepTx1_k1

""" + ''.join(f"#print axioms PRVEq.CallerPrepTx1_k1.{n}\n" for n in ['c_off_semantic','c_off_y1','c_off_inactive','c_logical_semantic','c_off_folded_root','c_off_round1','c_error_inst']+[b.replace('.','_')+'_eq' for b in needx]+['bound_exists'])
open(out,'w').write(hdr+fragtxt+'\n'+'\n'.join(bound+extras)+'\n'+tail)
json.dump(dict(classes=classes,extras=[s for _,s,_ in EX],cps=cpairs,x_blocks=needx),open(out+'.classes.json','w'),indent=1)
print('wrote',out,len(fields),'fields',len(eqs),'eqs',len(cpairs),'cps')
