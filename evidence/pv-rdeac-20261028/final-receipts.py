from pathlib import Path
import json,re,hashlib,datetime,subprocess,collections
D=Path(__file__).parent
pins={r['module']:r for r in json.loads((D/'final-source-pins.json').read_text())}
frozen=(D/'revision.txt').read_text().strip()
def metric(p):
 s=p.read_text();r={}
 for k,pat in [('wall_time',r'Elapsed.*: (.+)'),('peak_rss_KiB',r'Maximum resident set size \(kbytes\): (\d+)'),('swaps',r'Swaps: (\d+)'),('time_exit',r'Exit status: (\d+)')]:
  m=re.search(pat,s);r[k]=m[1] if m else None
 return r
rows=[]
for i in range(61100,61200):
 r=json.loads((D/f'receipt-{i}.json').read_text());out=(D/f'out-{i}.log').read_text()
 r.update(metric(D/f'time-{i}.log'));r['print_axioms']=[s for s in out.splitlines() if 'axioms' in s];r['errors']=[s for s in out.splitlines() if 'error:' in s or 'error(' in s]
 r['proof_credit']=r['exit']==0 and not any('sorryAx' in s for s in r['print_axioms'])
 pin=pins.get(r['target']);r['source_path']=pin['path'] if pin else 'removed failed NativeStop draft; see failed-61196-source.lean.txt'
 r['source_blob_at_freeze']=pin['blob'] if pin and pin['source_sha256']==r['source_sha256'] else None
 r['source_revision_at_freeze']=frozen if r['source_blob_at_freeze'] else None
 r['launch_revision']=r.pop('revision');r['working_source_note']='Launch HEAD plus exact compiled source SHA; pre-commit working sources are not represented as clean-HEAD compilations. Freeze revision/blob is supplied only when byte-identical.'
 snap=D/'attempt-sources'/f'{i}.lean.txt'
 if snap.exists():assert hashlib.sha256(snap.read_bytes()).hexdigest()==r['source_sha256'];r['source_snapshot']=str(snap.relative_to(D))
 r['caps']=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,lean_M=7000)
 rows.append(r)
(D/'attempts.json').write_text(json.dumps(rows,indent=2)+'\n')
native=[]
for i in range(1,6):
 label=f'native{i:02}';r=json.loads((D/f'{label}-receipt.json').read_text());r.update(metric(D/f'{label}-time.log'));r['print_axioms']='N/A: native finite validation / read-only source/image aggregation';native.append(r)
(D/'native-scopes.json').write_text(json.dumps(native,indent=2)+'\n')
refusals=[]
for p in sorted(D.glob('admission-*-refused*.json')):
 r=json.loads(p.read_text());assert r.get('allowed') is False,p
 refusals.append(dict(path=p.name,utc=r.get('utc'),reason=r.get('reason'),bounded_reserved_bytes=r.get('bounded_reserved_bytes')))
# Mechanically check receipt/admission signals and cooldown for every actual launch.
slips=[]
ref_times=[datetime.datetime.fromisoformat(r['utc']).timestamp() for r in refusals if r['utc']]
for r in rows+native:
 label=str(r['attempt']) if 'attempt' in r else r['label'];p=D/f'admission-{label}.json';a=json.loads(p.read_text())
 assert a['allowed'] is True and r['admission_allowed'] is True and r['admission_exit']==0,label
 t=datetime.datetime.fromisoformat(a['utc']).timestamp();prior=[x for x in ref_times if x<t]
 if prior and t-max(prior)<180:slips.append(dict(label=label,elapsed=t-max(prior)))
assert not slips,slips
summary=dict(lean_attempts=len(rows),successful=sum(r['exit']==0 for r in rows),failed=sum(r['exit']!=0 for r in rows),native_scopes=len(native),kani=0,refusals=refusals,admission_slips=slips,peak_lean_RSS_KiB=max(int(r['peak_rss_KiB']) for r in rows),peak_native_RSS_KiB=max(int(r['peak_rss_KiB']) for r in native),all_swaps_zero=all(r['swaps']=='0' for r in rows+native),final_statement_audit=61197,axioms_audit=61198,final_replay=dict(id=61199,exit=1,reason='Copied physical theorem used unqualified endpoint; corrected replay source is pending compilation after budget exhaustion'),audited_axioms_lines=len(rows[98]['print_axioms']),audited_bad_axioms=[s for s in rows[98]['print_axioms'] if any(x in s for x in ['sorryAx','axiom '])])
assert summary['lean_attempts']==100 and summary['audited_axioms_lines']==108 and not summary['audited_bad_axioms']
(D/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
p=Path('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RDEAC_EndpointReplay.lean')
(D/'pending-replay.json').write_text(json.dumps(dict(module='R1Z.PV_RDEAC_EndpointReplay',failed_id=61199,failed_source_sha256=rows[99]['source_sha256'],corrected_source_path=str(p),corrected_source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),corrected_source_git_blob=subprocess.check_output(['git','hash-object',str(p)],text=True).strip(),validated=False,reason='Attempt budget exhausted. No reuse of ID61199, no outside-range compile, no native-scope Lean workaround.'),indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['refusals']}))
