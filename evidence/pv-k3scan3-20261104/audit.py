"""Final artifact audit only: no compiler, solver, network, or source mutation."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess,collections
E=Path(__file__).resolve().parent;ROOT=E.parents[1]
read=lambda p:json.loads((E/p).read_text())
assert str(ROOT)=='/Users/dominic/ZK/.worktrees/pv-k3scan'
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/pv-k3scan-20261101'
setup={91900,91904,91905};diagnostic={91903};positive={91901,91906,91908,91910,91912,91914,91916,91918,91920,91921}
receipts={};features={};failures={};starts=[]
for i in range(91900,91960):
 ident='K'+str(i);d=E/'host'/ident;r=json.loads((d/'receipt.json').read_text());receipts[ident]=r
 assert r['id']==ident and (d/'time.log').exists()
 assert r['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64}
 assert r['swap']==0 and r['peak_rss_kib']>0 and r['wall_seconds']>0
 assert read(f'host/{ident}/admission.json')['allowed'] is True
 barrier=read(f'host/{ident}/barrier.json');assert barrier['allowed'] is True
 assert barrier['own_limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 quiet=read(f'host/{ident}/quiet-marker.json');assert quiet['marker'] is None or quiet['now']>=quiet['marker']['until']
 st=read(f'host/{ident}/STARTED.json');starts.append((st['epoch'],st['epoch']+r['wall_seconds'],ident))
 log=(d/'output.log').read_text()
 if i in setup:assert 'could not compile' in log and 'VERIFICATION:-' not in log
 elif i in diagnostic:assert 'Failed Checks: attempt to add with overflow' in log
 elif i in positive:assert r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log
 else:
  assert r['negative_control'] and r['exit_status']==1 and 'VERIFICATION:- FAILED' in log and 'Failed Checks:' in log
  checked=log.split('Failed Checks:',1)[1].split('VERIFICATION:-',1)[0];failures[ident]=checked.strip()
  assert 'unwinding assertion' not in checked.lower() and 'arithmetic overflow' not in checked.lower()
 md=read(f'host/{ident}/metadata.json');features[ident]={p['name']+':'+p['version']:n['features'] for n in md['resolve']['nodes'] for p in md['packages'] if p['id']==n['id']}
 if i>=91906:
  core=next(v for k,v in features[ident].items() if k.startswith('aspis-core:'))
  assert {'ct-host-prover','r0'}<=set(core) and 'r0-op-count' not in core
 assert r['print_axioms']=='N/A: Kani; 0 Lean'
for a,b in zip(sorted(starts),sorted(starts)[1:]):assert a[1]<=b[0]+0.05,(a,b)
ref=read('host/K91921/refusals/0/barrier.json');assert not ref['allowed'] and 'FileNotFoundError' in ref['error']
assert not (E/'host/K91921/refusals/0/time.log').exists()
old=read('host/K91921/refusals/0/STARTED.json');fresh=read('host/K91921/STARTED.json');assert fresh['epoch']-old['epoch']>=180
index=read('SOURCE-INDEX.json');assert index['missing']==[] and index['resolved']==index['input_hashes']==178
for p in E.glob('*.sha256'):
 b=lzma.decompress(p.with_suffix('.xz').read_bytes()) if p.with_suffix('.xz').exists() else p.with_suffix('').read_bytes()
 assert hashlib.sha256(b).hexdigest()==p.read_text().strip(),p
for n,d in read('TOOL-PINS.json')['tools'].items():assert d['sha256']==json.loads((E.parent/'pv-k3scan-20261101/D549-TOOL-PINS.json').read_text())['tools'][n]['sha256']
assert read('ASSOCIATION.json')['compiled_harness_stub_oracle_no_static_tokens']
# Explicit matched pairs and exact selected source footprints. Adding the
# unselected repeat module did not change q/qs/mutation or the selected caller.
pairs={91901:[91902],91906:[91907],91908:[91909],91910:[91911],91912:[91913],91914:[91915,91922,91923],91916:[91917,*range(91954,91960)],91918:[91919,*range(91948,91954)],91920:list(range(91924,91936)),91921:list(range(91936,91948))}
pair_records=[]
for p,ns in pairs.items():
 for n in ns:
  a=receipts['K'+str(p)];b=receipts['K'+str(n)];assert a['config']['harness']==b['config']['harness']
  x=read(f'host/K{p}/source-sha256.json');y=read(f'host/K{n}/source-sha256.json')
  different={k for k in x.keys()|y.keys() if x.get(k)!=y.get(k)}
  assert different<={'caller/lib.rs','caller/repeat_context.rs'},(p,n,different)
  if different:
   def input_bytes(h):
    origin=index['sources'][h]
    if 'file' in origin:return (E/origin['file']).read_bytes()
    assert 'git_blob' in origin,origin
    return subprocess.check_output(['git','cat-file','blob',origin['git_blob']])
   old_root=input_bytes(x['caller/lib.rs']);new_root=input_bytes(y['caller/lib.rs'])
   # Only the unselected C156 harness and its new module declaration changed.
   erased=new_root.replace(b'  if cfg!(feature="context") {crate::repeat_context::caller();return;}\n',b'').replace(b'\nmod repeat_context;\n',b'')
   assert erased==old_root,(p,n,'selected root changed')
  pair_records.append({'positive':'K'+str(p),'control':'K'+str(n),'harness':a['config']['harness'],'full_input_manifest_identical':not different,'unselected_source_changes':sorted(different),'selected_closure_unchanged':True,'control_failure':failures['K'+str(n)]})
assert len(pair_records)==46
protected=subprocess.check_output(['git','diff',read('PINS.json')['entry'],'--','crates','programs','design','docs/research/v8-r0-zk-20261009/lean'])
assert not protected
assert not any(p.stat().st_size>20*1024**2 for p in E.rglob('*') if p.is_file())
result={'status':'PASS','charged_Kani_invocations':60,'Lean_invocations':0,'positive_passes':len(positive),'expected_failing_controls':len(pair_records),'setup_failures':len(setup),'nondeployed_feature_diagnostic_failures':len(diagnostic),'uncharged_barrier_refusals':1,'application_counterexamples_established':0,'peak_rss_kib':max(r['peak_rss_kib'] for r in receipts.values()),'sum_wall_seconds':sum(r['wall_seconds'] for r in receipts.values()),'swap':0,'refusal_retry_gap_seconds':fresh['epoch']-old['epoch'],'serial_scopes':True,'quiet_markers_captured':60,'unique_input_hashes_resolved':178,'tool_binaries_match_pinned_predecessor':6,'endpoint_premises_removed_added_weakened':[0,0,0],'deployed_std_transfer':'WITHHELD; new reached-item comparison not performed','C156':'SUSPENDED: actual full-raw multiplication child bridge/G substitution missing','axioms':'N/A: zero Lean; reused RDCD4 summary-based audit attributed separately'}
(E/'PAIRS.json').write_text(json.dumps(pair_records,indent=2)+'\n');(E/'FEATURES.json').write_text(json.dumps(features,indent=2)+'\n');(E/'VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
