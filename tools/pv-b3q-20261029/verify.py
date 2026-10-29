from pathlib import Path
import json,hashlib,re,subprocess,datetime
D=Path('evidence/pv-b3q-20261029');H=D/'host';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();allowed={'propext','Classical.choice','Quot.sound'}
rows=[];ids=set();failed=set();source_errors=[];admissions=[];refusals=[]
for p in sorted((H/'receipts').glob('lean-*/receipt/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];assert 70200<=a<=70299 and a not in ids,a;ids.add(a)
 source=p.parent.parent/'source.lean';assert sha(source)==r['source_sha256'],p
 raw=subprocess.check_output(['git','show',r['source_revision']+':evidence/pv-b3q-20261029/lean/'+r['module']+'.lean'])
 assert hashlib.sha256(raw).hexdigest()==r['source_sha256'],(a,'source revision mismatch')
 if r['exit_status']!=0:assert r['source_sha256']not in failed;failed.add(r['source_sha256'])
 rows.append(dict(attempt=a,module=r['module'],exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],source_sha256=r['source_sha256'],receipt=str(p.relative_to(D))))
assert ids==set(range(70200,70278))|{70297,70298,70299},sorted(ids)
# Exact duplicate failing input is disallowed even if the second result passed.
for digest in failed:assert sum(r['source_sha256']==digest for r in rows)==1,digest
# Successful scope admission and caps, plus all refused-launch cooldowns.
receipts=list((H/'receipts').glob('lean-*/receipt/receipt.json'))+list((H/'receipts').glob('native-*/receipt/receipt.json'))
parse_time=lambda s:datetime.datetime.fromisoformat(s).timestamp()
for parent in (H/'receipts').iterdir():
 if not parent.is_dir():continue
 for name in ['reservation.json','barrier.json']:
  p=parent/name
  if p.exists():
   x=json.loads(p.read_text())
   if x.get('allowed') is False:refusals.append(dict(label=parent.name,gate=name,epoch=parse_time(x['utc'])))
for p in receipts:
 r=json.loads(p.read_text());parent=p.parent.parent;reservation=json.loads((parent/'reservation.json').read_text());barrier=json.loads((parent/'barrier.json').read_text())
 assert reservation['allowed']is True and barrier['allowed']is True,parent
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},parent
 assert r['swaps']==0 and r['peak_rss_kib']<8*1024*1024,parent
 start=parse_time(reservation['utc']);earlier=[x['epoch']for x in refusals if x['epoch']<start]
 recovery=start-max(earlier)if earlier else None
 assert recovery is None or recovery>=180,(parent,recovery)
 admissions.append(dict(label=parent.name,reservation_allowed=True,barrier_allowed=True,recovery_seconds=recovery))
# Accepted final theorem audit, with multiline axiom reports parsed in full.
f=json.loads((D/'frozen-manifest.json').read_text());audit=next(r for r in rows if r['attempt']==70298);log=(D/audit['receipt']).parent/'stdout.log';text=log.read_text();seen={}
for name,axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S):
 found={a.strip()for a in axioms.split(',')if a.strip()};assert found<=allowed,(name,found);seen[name]=sorted(found)
for name in re.findall(r"'([^']+)' does not depend on any axioms",text):seen[name]=[]
assert set(seen)==set(f['theorems']),(set(f['theorems'])-set(seen),set(seen)-set(f['theorems']))
for source in f['sources']:assert sha(Path(source['path']))==source['sha256'],source
for a in [70297,70298,70299]:assert next(r for r in rows if r['attempt']==a)['exit']==0
pre=json.loads((H/'preaudit-freeze.json').read_text());assert pre['status']=='pass'and pre['accepted_source_count']==47
# Scope-specific concrete comparisons and perturbation controls.
assert json.loads((H/'d188-positive-comparison.json').read_text())['mismatches']==[]
assert json.loads((H/'d188-negative-comparison.json').read_text())['mismatches']==['absorption_lanes_literal:0']
assert json.loads((H/'matrix-emission-comparison.json').read_text())['entries']==36
assert json.loads((H/'matrix-raw-emission-comparison.json').read_text())['entries']==90
native=[]
for p in sorted((H/'receipts').glob('native-*/receipt/receipt.json')):
 r=json.loads(p.read_text());label=p.parent.parent.name;expected=1 if label.startswith('native-d188-negative')else 101 if label.endswith('negative')else 0
 if label=='native-d188-positive-r1':expected=101
 assert r['exit_status']==expected,(label,r['exit_status'],expected)
 native.append(dict(label=label,exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],receipt=str(p.relative_to(D))))
assert len(native)<=30 and not list(H.rglob('*.olean*'))
assert 'Arguments::as_str=None; numeric payload=17' in (H/'receipts/native-format-placeholder-positive/receipt/stdout.log').read_text()
assert 'numeric Display propagates the writer Err' in (H/'receipts/native-format-placeholder-negative/receipt/stderr.log').read_text()
# Every accepted theorem is standard-only; the actual formatter diagnostics are quarantined.
quarantined=[r for r in rows if r['module']=='PV_B3Q_FormatCounterexample'and r['exit']==0]
assert {r['attempt']for r in quarantined}=={70267,70269}
for r in quarantined:assert 'core.fmt.Formatter' in ((D/r['receipt']).parent/'stdout.log').read_text()
assert not any('FormatCounterexample'in m for m in f['proof_modules'])
branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip();assert branch=='codex/pv-b3q-20261029'
paths=subprocess.check_output(['git','diff','--name-only','15819d2768..HEAD'],text=True).splitlines();assert all(p.startswith(('evidence/pv-b3q-20261029/','tools/pv-b3q-20261029/'))for p in paths)
out=dict(status='pass for accepted frozen scope; complete std/dependency catalogue OPEN',branch=branch,base='15819d2768e2ed80a614edae6aa5d7dcb9055e84',verification_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),lean_attempts=len(rows),lean_compile_passes=sum(r['exit']==0 for r in rows),lean_rejections=sum(r['exit']!=0 for r in rows),accepted_frozen_modules=len(f['sources']),audited_theorems=len(seen),axioms_allowed=sorted(allowed),theorem_axioms=seen,lean_receipts=rows,native_scopes=len(native),native_receipts=native,kani_runs=0,refused_gates=len(refusals),minimum_recovery_seconds=min(a['recovery_seconds']for a in admissions if a['recovery_seconds']is not None),admissions=admissions,void_compiles=0,unchanged_failed_source_resubmissions=0,quarantined_lean_attempts=[r['attempt']for r in quarantined],full_manifest_replays=1,remaining_lean_budget=100-len(rows),remaining_native_budget=30-len(native),stop='Affected full-catalogue step blocked by pinned formatter axioms-audit discrepancy and checked rejecting-writer counterexample to the unconditional always-Ok interpretation. Other requested restoration/matrix evidence completed. No endpoint counterexample or privacy closure claimed.',premises_removed=[],premises_added=[],T_changed=False,V370_D381_D386='retained',implementation_changes=False,push=False,merge=False,key_operations=False)
(D/'verification-summary.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k in ['status','lean_attempts','lean_compile_passes','lean_rejections','audited_theorems','native_scopes','refused_gates','minimum_recovery_seconds','remaining_lean_budget']}))
