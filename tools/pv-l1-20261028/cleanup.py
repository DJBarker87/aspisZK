"""Remove only this job's rebuildable compiled scratch, after saving its hashes."""
import pathlib,json,subprocess,shlex
E=pathlib.Path(__file__).resolve().parents[2]/'evidence/pv-l1-20261028'
assert json.loads((E/'final-cache-id-check.json').read_text())['all_match']
assert all(json.loads((E/f'receipt-{i}.json').read_text())['accepted'] for i in [51697,51698,51699])
code=r'''import pathlib,shutil,json,datetime
p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-l1-20261028');assert p.is_dir() and not p.is_symlink();assert (p/'evidence/final-cache-id-check.json').is_file()
removed=[]
for name in ['objects','external']:
 q=p/name;assert q.parent==p and not q.is_symlink();count=sum(1 for f in q.rglob('*') if f.is_file());shutil.rmtree(q);removed.append(dict(path=str(q),files=count,exists_after=q.exists()))
r=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),removed=removed,preserved=['sources','evidence','J.json'],shared_paths_written=False,wallet_key_actions=False,reason='local-lean rule9; exact object hashes retained in final-cache-id-check.json')
(p/'evidence/cleanup.json').write_text(json.dumps(r));print(json.dumps(r))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True);assert r.returncode==0,r.stderr
(E/'cleanup.json').write_text(r.stdout);print(r.stdout)
