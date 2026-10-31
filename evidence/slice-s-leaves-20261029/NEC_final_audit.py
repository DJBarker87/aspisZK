from pathlib import Path
import json,re,hashlib,subprocess,lzma,collections
E=Path(__file__).resolve().parent;root=E.parent.parent
rows=[json.loads(l) for l in (E/'NEC_ATTEMPTS.jsonl').read_text().splitlines()]
def raw(p):return p.read_bytes() if p.exists() else lzma.decompress(p.with_name(p.name+'.xz').read_bytes())
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in rows:
 assert r['limits']==limits and str(r['swaps'])=='0',r['attempt']
 admission=json.loads((E/(r['attempt']+'-admission.json')).read_text());assert admission['exit']==0 and admission['reservation']['allowed'] is True
 if r['kind']=='kani':
  lock=json.loads((E/(r['attempt']+'-lock-check.json')).read_text());assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  graph=json.loads((E/(r['attempt']+'-graph-check.json')).read_text());assert graph['exact_frozen_selected_graph']
assert collections.Counter(r['kind'] for r in rows)==dict(kani=80,lean=78,extract=9)
axioms=next(r for r in rows if r['attempt']=='NEC_L078');assert axioms['exit_status']==0
for line in axioms['print_axioms']:
 assert 'sorryAx' not in line and 'axiom ' not in line
 if '[' in line:assert set(line.rsplit('[',1)[1].rstrip(']').split(', '))<= {'propext','Classical.choice','Quot.sound'}
latest={}
for r in rows:
 if r['kind']=='lean' and r['exit_status']==0:latest[r['module']]=r
accepted=[]
for module,r in latest.items():
 p=E/(module+'.lean');assert p.exists(),module
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_hashes']['NEC_generated/'+module+'.lean'],module
 assert not re.search(r'\b(sorry|admit|native_decide)\b', '\n'.join(l for l in p.read_text().splitlines() if not l.lstrip().startswith('--'))),module
 accepted.append(dict(module=module,receipt=r['receipt'],sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
large=[str(p.relative_to(E)) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024];assert not large,large
assert not subprocess.check_output(['git','diff','--name-only','4bb3b3f5','--','crates','programs'],cwd=root).strip()
assert json.loads((E/'NEC_SOURCE_HISTORY.json').read_text())['all_recorded_source_pin_hashes_exact']
peaks=[int(r['peak_rss_kib']) for r in rows if str(r['peak_rss_kib']).isdigit()]
x=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),budget_used=dict(collections.Counter(r['kind'] for r in rows)),budget_remaining=dict(kani=0,lean=2,extract=11),accepted_modules=accepted,axioms_audit='NEC_L078/receipt.json',axioms_theorems=len(axioms['print_axioms']),peak_rss_kib=max(peaks),swaps=0,all_admissions_allowed_exit0=True,all_caps_exact=True,all_native_locks_frozen_unchanged=True,all_native_graphs_frozen=True,full_source_histories_exact=80,shipped_crates_programs_frozen=True,files_over20MiB=[],local_conditional_packet_proposals=2,new_composed_closed_rows=0,current_ndt='report snapshot refresh required; baseline-only validation passed',push=False,full_release_replay=False)
(E/'NEC_FINAL_AUDIT.json').write_text(json.dumps(x,indent=1)+'\n')
print('Audit passed:',x['budget_used'],'axioms',x['axioms_theorems'],'peakKiB',x['peak_rss_kib'])
