"""Read-only result/source checks plus a generated evidence index; no jobs."""
from pathlib import Path
import json,re,hashlib,subprocess
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw-step-20261026'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lean=[];latest={}
for p in sorted(e.glob('*-receipt.json')):
 x=json.loads(p.read_text())
 if 'attempt' not in x or not isinstance(x['attempt'],int):continue
 a=x['attempt'];assert 23700<=a<=23999
 assert sha(e/f'{a}.lean.txt')==x['source_sha256']
 dep=json.loads((e/x['dependencies_manifest']).read_text())
 assert hashlib.sha256(json.dumps(dep,sort_keys=True).encode()).hexdigest()==x['deps_fingerprint']
 t=x['time_log'];metric=lambda pat:re.search(pat,t).group(1) if re.search(pat,t) else None
 if x['exit_status']==0:
  assert x['print_axioms'] and not x['errors']
  for report in x['print_axioms']:
   if 'depends on axioms:' in report:
    names=set(z.strip() for z in report.split('depends on axioms: [')[1].split(']')[0].split(','))
    assert names<={'propext','Classical.choice','Quot.sound'},(a,report)
  latest[x['module']]=x
 lean.append(dict(attempt=a,module=x['module'],exit=x['exit_status'],wall=metric(r'Elapsed .*: (.*)'),peak_rss_kib=metric(r'Maximum resident set size \(kbytes\): (.*)'),swap=metric(r'Swaps: (.*)'),axioms=x['print_axioms'],source_sha256=x['source_sha256']))
for p in sorted((e/'local').glob('*-receipt.json')):
 x=json.loads(p.read_text());a=x['attempt']
 assert 23700<=a<=23999 and a not in [z['attempt'] for z in lean]
 snap=p.parent/x['source_snapshot'] if x.get('source_snapshot') else None
 if snap:assert sha(snap)==x['source_sha256']
 if x['exit_status']==0:
  assert x['print_axioms']
  for report in x['print_axioms']:
   if 'depends on axioms:' in report:
    names=set(z.strip() for z in report.split('depends on axioms: [')[1].split(']')[0].split(','))
    assert names<={'propext','Classical.choice','Quot.sound'},(a,report)
  latest.setdefault(x['module'],x)
 lean.append(dict(attempt=a,module=x['module'],exit=x['exit_status'],wall=x.get('wall_seconds'),peak_rss_bytes=x.get('peak_rss_bytes'),swap=x.get('swaps'),axioms=x['print_axioms'],source_sha256=x.get('source_sha256'),kind='local'))
assert len(lean)<=100
modules=[]
for p in sorted((r/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RW_*.lean')):
 m='R1Z/'+p.stem
 assert m in latest,('not green',m)
 assert sha(p)==latest[m]['source_sha256'],('current differs from accepted',m)
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M),p
 modules.append(dict(module=m,attempt=latest[m]['attempt'],source_sha256=sha(p)))
native=[];bound_map={'compression_state_step':2,'compression_accumulator_c0a':2,'primitive_split::scale_c0a':2,'primitive_split::add_c0a':2,'compression_iterator16_next':18,'scalar_mul_wrapper':2,'compression_m31_suffix_next':18,'compression_initial_state':2,'reduce64_wrapper':2,'sampler_single_limb':2,'sampler_reverse_iterator_next':10,'scalar_product_casts':2,'scalar_mul_literal_body':2,'compression_step_matched_borrow':2,'compression_matched_accumulator_c0a':2,'sampler_array_state_step':10,'compression_matched_power_c0a':2,'sampler_load_word_step':34,'sampler_load_words_all':34,'sampler_decode_words':34}
for p in sorted(e.glob('pv-rw-step-*/receipt.json')):
 x=json.loads(p.read_text());cmd=x['target'];kani='kani' in cmd
 if not kani:continue
 harness=cmd[cmd.index('--harness')+1];bound=bound_map[harness]
 log=(p.parent/'stdout.log').read_text()
 if x['exit_status']==0:assert 'VERIFICATION:- SUCCESSFUL' in log and '0 failures' in log
 assert x['exit_status'] in [0,124]
 assert '--unwinding-assertions' in cmd
 assert x['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 for f in (p.parent/'inputs').rglob('*'):
  if f.is_file():assert sha(f)==x['source_sha256']['tools/prover-rw-20261023/pv-rw-step/'+str(f.relative_to(p.parent/'inputs'))]
 native.append(dict(attempt=x['attempt'],harness=harness,bound=bound,exit=x['exit_status'],result='PASS' if x['exit_status']==0 else 'timeout; no certificate',wall_seconds=x['wall_seconds'],cgroup_memory_peak_bytes=x['cgroup_memory_peak_bytes'],swap_peak_bytes=x['cgroup_swap_peak_bytes'],source_revision_label=x['source_revision']))
assert len(native)==20
changed=subprocess.check_output(['git','diff','--name-only','5d97a425c5','--','crates','programs'],cwd=r,text=True).strip();assert not changed
summary=dict(base='5d97a425c5',branch=subprocess.check_output(['git','branch','--show-current'],cwd=r,text=True).strip(),lean_budget=100,lean_used=len(lean),lean_remaining=100-len(lean),lean_passes=sum(x['exit']==0 for x in lean),kani_budget=20,kani_used=len(native),kani_passes=sum(x['exit']==0 for x in native),kani_timeouts=sum(x['exit']==124 for x in native),accepted_modules=modules,lean=lean,kani=native,ledger_rows_removed=[],endpoint_premises_removed=[],target_established=False,scope='Focused cached source checks. No coherent release replay, deployment adoption or native full compression certificate.')
(e/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
lines=['# Kani split table','','Every row has its own preflight, full output, resource receipt and exact Rust input snapshots. All use no stubs,6G/8G/swap0/Tasks64 and a240-second timeout.','','| Harness | Bound | Result | Wall seconds | Receipt |','| --- | ---: | --- | ---: | --- |']
for x in sorted(native,key=lambda x:int(x['attempt'].rsplit('-',1)[1])):lines.append(f"| `{x['harness']}` | {x['bound']} | {x['result']} | {x['wall_seconds']:.2f} | [{x['attempt']}]({x['attempt']}/receipt.json) |")
(e/'KANI-SPLITS.md').write_text('\n'.join(lines)+'\n')
print({k:summary[k] for k in ['lean_used','lean_remaining','lean_passes','kani_used','kani_passes','kani_timeouts','ledger_rows_removed']})
