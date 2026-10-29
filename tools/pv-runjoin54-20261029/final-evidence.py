from pathlib import Path
import subprocess,json,hashlib,lzma,datetime
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin54-20261029';base='1adf3ca50f50b8983de4eeb9609731a1301ca463'
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=R).strip()
paths=subprocess.check_output(['git','diff','--name-only',base,head],text=True,cwd=R).splitlines()
assert all(p.startswith(('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_','tools/pv-runjoin54-20261029/','evidence/pv-runjoin54-20261029/')) for p in paths)
assert not subprocess.check_output(['git','diff',base,head,'--','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_OWN*','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RJDec_*'],cwd=R)
plan=json.loads((E/'build-plan.json').read_text());rows=[]
for m in ['R1Z.PV_AL_CircleOwnedTypes','AspisR72Sampler.Types']:
 v=plan['modules'][m];p=v['path'];before=subprocess.check_output(['git','show',base+':'+p],cwd=R);after=(R/p).read_bytes();assert before==after
 rows.append(dict(module=m,path=p,source_sha256=hashlib.sha256(after).hexdigest(),entry_source_identical=True,authority=v['authority'],pinned_source_sha256=v['sha256']))
(E/'collision-authorities-unchanged.json').write_text(json.dumps(rows,indent=2)+'\n')
(E/'changed-paths-check.json').write_text(json.dumps(dict(base=base,checked_head=head,only_assigned_paths=True,protected_prefix_diff_empty=True,paths=paths),indent=2)+'\n')
scopes=[]
for p in E.glob('receipt-*.json'):
 x=json.loads(p.read_text());t=json.loads((E/f"transport-{x['attempt']}.json").read_text());start=datetime.datetime.fromisoformat(x['utc']).timestamp();scopes.append(dict(attempt=x['attempt'],recorded_submission_epoch=start,transport_wall=t['wall'],recorded_transport_end_epoch=start+t['wall']))
scopes.sort(key=lambda x:x['recorded_submission_epoch'])
assert all(a['recorded_transport_end_epoch']<=b['recorded_submission_epoch'] for a,b in zip(scopes,scopes[1:]))
(E/'scope-sequence.json').write_text(json.dumps(dict(nonoverlapping_recorded_submissions=True,rows=scopes),indent=2)+'\n')
p=E/'fresh-preflight.json'
if p.exists():p.rename(E/'final-preflight.json')
for n in ['final-preflight.json','current-head-source-check.json']:
 p=E/n
 if p.exists():
  b=p.read_bytes();Path(str(p)+'.xz').write_bytes(lzma.compress(b));Path(str(p)+'.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n');p.unlink()
for p in E.rglob('*'):
 assert not (p.is_file() and p.stat().st_size>20_000_000),p
print('Changed paths, protected prefixes, collision authorities, scope sequence and metadata sizes verified')
