"""Read-only formal receipts and source/object inventory for this continuation."""
from pathlib import Path
import json,hashlib,re,subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-batch3-20261027')
t=json.loads((H/'TALLY-d324.json').read_text());records=[]
for r in t['receipts']:
 if r['attempt']<37916:continue
 p=Path(r['receipt']);rec=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()+(p.parent/'stderr.log').read_text()
 reports=[]
 for m in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log):
  reports.append({'declaration':m[1],'axioms':[x.strip()for x in m[2].split(',') if x.strip()]})
 for m in re.finditer(r"'([^']+)' does not depend on any axioms",log):reports.append({'declaration':m[1],'axioms':[]})
 bad=sorted({a for x in reports for a in x['axioms'] if a not in ['propext','Classical.choice','Quot.sound']})
 rec['complete_axiom_reports']=reports;rec['nonstandard_axioms_in_log']=bad
 rec['credited']=rec['exit_status']==0 and not bad
 records.append(rec)
accepted=[r for r in records if r['credited']]
assert len(records)==79,len(records)
assert all(r['swaps']==0 for r in records)
assert all(not r['nonstandard_axioms_in_log'] for r in accepted)
source=json.loads((H/'d324-source.json').read_text());bad=[]
for n,s in source['files'].items():
 p=H/'source'/n;a=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file()else None
 if a!=s:bad.append({'path':n,'expected':s,'actual':a})
assert not bad,bad
objects=[{'path':str(p),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}for p in (H/'lean-objects').rglob('*')if p.is_file()and '.olean' in p.name]
(H/'d324-object-inventory.json').write_text(json.dumps(objects,indent=2)+'\n')
retained=[]
for name in ['batch3b-split-counterexample','batch3c-split-counterexample']:
 p=H/'bin'/name;retained.append({'path':str(p),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
active=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=active','--plain','--no-legend']).decode()
own=[s for s in active.splitlines() if 'pv-b3-' in s and ('lean-379' in s or 'd324-' in s)]
assert not own,own
cooldowns=[]
for old,new in [(37981,37982),(37983,37984),(37990,37991),(37993,37994),(37995,37996)]:
 r=H/f'lean-{old}';q=r/'refusal.json'
 if not q.exists():q=r/'barrier.json'
 gap=(H/f'lean-{new}'/'target.json').stat().st_mtime-q.stat().st_mtime
 assert gap>=180,(old,new,gap)
 cooldowns.append({'refused_id':old,'retry_id':new,'wall_gap_seconds':gap})
result={'rust_source_revision':source['revision'],'charged_this_resume':len(records),'accepted_this_resume':len(accepted),
 'rejected_this_resume':len(records)-len(accepted),'kani':0,'allocated_ids_consumed':list(range(37916,38000)),
 'charged_budget_remaining':85-len(records),'authorized_ids_remaining':[],
 'allocation_status':'all assigned IDs consumed; six more fresh charged-attempt IDs requested; none allocated independently',
 'refusals_this_resume':[r for r in t['refusals']if r['attempt']>=37916],'cooldowns':cooldowns,
 'all_lean_swap_zero':True,'maximum_lean_peak_rss_kib':max(r['peak_rss_kib'] for r in records),
 'accepted_nonstandard_axioms':[], 'source_files_rechecked':len(source['files']),'source_mismatches':bad,
 'retained_counterexamples':retained,'active_own_scopes':own,'private_cache_retained_for_pending_continuation':True,
 'keys_deleted':False,'nonce_ledgers_deleted':False,'shared_sources_or_objects_written':False,'receipts':records}
(H/'d324-receipt-index.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ['receipts','retained_counterexamples','allocated_ids_consumed']},indent=2))
