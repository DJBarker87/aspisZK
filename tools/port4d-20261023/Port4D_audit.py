#!/usr/bin/env python3
"""Static source, final target, standard-axiom and resource audit; no prover."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]; L=R/'docs/research/100bit-spend-path-20261013/lean'; E=R/'evidence/port4d-20261023'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
compact=lambda s: re.sub(r'\s+','',s)
base='986dc0bd7daf04ecd14cd0459585855277fef937'
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
allowed=lambda p:p.startswith(('evidence/port4d-20261023/','tools/port4d-20261023/','docs/research/100bit-spend-path-20261013/lean/Port4D_'))
assert all(map(allowed,changed+untracked)),[p for p in changed+untracked if not allowed(p)]
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('*/receipt.json'))]
leans=[r for r in receipts if r['kind']=='lean']; assert len(leans)<=100
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in receipts:
 assert r['limits']==limits,(r['attempt'],r['limits'])
 assert r['swaps']=='0',r['attempt']
 for name,h in r['source_hashes'].items():assert sha(E/r['attempt']/'sources'/name)==h
 if r['kind']=='charon':
  for name,h in r['source_hashes'].items():
   local=R/name.removeprefix('src/')
   assert sha(local)==h,(local,h)
modules={}
for p in sorted(L.glob('Port4D_*.lean')):
 s=p.read_text(); code=re.sub(r'/\-[\s\S]*?\-/|--[^\n]*','',s); assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b',code),p
 accepted=[r for r in leans if r['exit_status']==0 and r['source_hashes'].get(p.name)==sha(p)]
 assert accepted, p.name
 r=accepted[-1]
 for line in r['print_axioms']:
  axioms=re.search(r'depends on axioms: \[([^\]]*)\]',line)
  if axioms:assert set(re.split(r',\s*',axioms[1].strip()))<={'propext','Classical.choice','Quot.sound'},line
 for theorem in re.findall(r'^theorem\s+([A-Za-z0-9_]+)',s,re.M):
  assert any("."+theorem+"'" in line for line in r['print_axioms']),(p.name,theorem)
 modules[p.stem]={'sha256':sha(p),'accepted_attempt':r['attempt'],'axioms':r['print_axioms']}
# Exact emitted current round, with visible leaf/carrier substitutions only.
s=(E/'current-round/Funs.lean.txt').read_text(); a=s.index('def verifier.finish_relation_round');b=s.index('\nend Port4D_Children',a);s=s[a:b]
s=s.replace('def verifier.finish_relation_round','def round (ops : FinishOps W)')
for old,new in [('weights.field','ops.field'),('weights.QUARTER','ops.quarter'),('aspis_core.field.wide_exact.WideExact.add','ops.add'),('aspis_core.field.wide_exact.WideExact.mul_m31','ops.mulM'),('trace.value','ops.trace'),('verifier.polynomial','ops.polynomial')]:s=s.replace(old,new)
s=re.sub(r'core.cmp.PartialEq.ne.trait_default\s+aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact','ops.ne',s)
actual=(L/'Port4D_Round.lean').read_text().split('def round',1)[1].split('theorem checked_mul',1)[0]
assert compact(s)==compact('def round'+actual),'round normalization'
# Current emitted value: map is an explicit local pure-library leaf.
s=(E/'current-value/Funs.lean.txt').read_text();a=s.index('def verifier.BatchedWeights.value');b=s.index('/--',a);s=s[a:b]
s=s.replace('def verifier.BatchedWeights.value','def native (map : Array U64 4#usize → Result (Array U32 4#usize))')
s=s.replace('core.array.Array.map (BuiltinFnMut Std.U64 aspis_core.field.M31) a\n      (aspis_core.field.M31.reduce_u64)','map a')
actual=(L/'Port4D_Value.lean').read_text().split('def native',1)[1].split('theorem value_eq',1)[0]
assert compact(s)==compact('def native'+actual),'value normalization'
# Current mutable parent matches the retained Port3 typed native syntax,
# including the deferred-return ABI, with no native std object substitution.
s=(E/'current-value/Funs.lean.txt').read_text();a=s.index('def verifier.BatchedWeights.finish_loop.body');b=s.index('/-- [aspis_r1_cost_probe::verifier::candidate::tx1]',a);s=s[a:b]
s=s.replace('verifier.BatchedWeights.value self i','value self i')
s=s.replace('core.iter.adapters.enumerate.IteratorEnumerate.next\n      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT\n      aspis_core.field.QM31) iter','ops.next iter')
s=s.replace('core.iter.traits.iterator.Iterator.enumerate.trait_default\n      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT\n      aspis_core.field.QM31) im','ops.enumerate im')
for name in ['verifier.BatchedWeights.finish_loop.body','verifier.BatchedWeights.finish_loop','verifier.BatchedWeights.finish']:
 s=s.replace('def '+name+'\n','def '+name+' (ops : Ops)\n  (value : verifier.BatchedWeights → Usize → Result aspis_core.field.QM31)\n')
s=s.replace('verifier.BatchedWeights.finish_loop.body self','verifier.BatchedWeights.finish_loop.body ops value self').replace('verifier.BatchedWeights.finish_loop iter','verifier.BatchedWeights.finish_loop ops value iter')
actual=(L/'Port3_NativeFlushBody.lean').read_text().split('def verifier.BatchedWeights.finish_loop.body',1)[1].split('#print axioms',1)[0]
assert compact(s)==compact('def verifier.BatchedWeights.finish_loop.body'+actual),'flush normalization'
report={'schema':'port4d-focused-proof-packet-v1','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'base_revision':base,'lean_attempts':len(leans),'kani_runs':0,'modules':modules,'failed_lean_attempts':[r['attempt'] for r in leans if r['exit_status']!=0],'compiler_free_ids':['lean-010'],'limits':limits,'all_new_theorems_standard_axioms':True,'current_round_value_flush_normalizations':True,'shipped_changed':False,'full_frozen_replay':False,'elf_rebuilt':False,'historical_elf_pins':{'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','pool_prefix':'121f3e29'},'remaining_boundaries':['TrustedStd map4/mutable iterator content and runtime interpretation','Current S5 reducer binding, and session A S3/S4/S5/S9 laws named in finish','same-reader/physical parser/query binding','same-source saved-ten provenance and returned-twelve query arithmetic interpretation','global S2 oracle model order/runtime/artifact adoption']}
(E/'audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['lean_attempts','kani_runs','current_round_value_flush_normalizations','shipped_changed']}))
