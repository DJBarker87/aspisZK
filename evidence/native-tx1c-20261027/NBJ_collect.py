from pathlib import Path
import sys,json,subprocess,hashlib,tarfile,io
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBJ_host as h
r=h.remote_py(f'''from pathlib import Path
import json
b=Path({h.B!r});print(json.dumps({{p.name:p.read_text() for p in list(b.glob('NBJ_K*-graph.json'))+list(b.glob('NBJ_K*-metadata.stderr'))}}))''');assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():(E/n).write_text(s)
rows=[]
for p in sorted(E.glob('NBJ_*/receipt.json')):
 d=json.loads(p.read_text());row={k:d.get(k) for k in ['attempt','kind','source_revision','source_hashes','command','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}
 log=(p.parent/'stdout.log').read_text();row['timeout']='timed out' in log.lower() or d['exit_status']==124
 rows.append(row)
(E/'NBJ_ATTEMPTS.json').write_text(json.dumps(dict(lean_attempts=sum(x['kind']=='lean' for x in rows),kani_runs=sum(x['kind']=='kani' for x in rows),rows=rows),indent=2)+'\n')
ar=subprocess.check_output(['git','archive','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','crates','programs','Cargo.toml','Cargo.lock']);expected={}
with tarfile.open(fileobj=io.BytesIO(ar)) as t:
 for m in t:
  if m.isfile():expected[m.name]=hashlib.sha256(t.extractfile(m).read()).hexdigest()
assert all(hashlib.sha256((R/n).read_bytes()).hexdigest()==sha for n,sha in expected.items())
(E/'NBJ_LOCAL_SOURCE_AUDIT.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',files=expected,all_match=True),indent=2)+'\n')
print(json.dumps(dict(lean=sum(x['kind']=='lean' for x in rows),kani=sum(x['kind']=='kani' for x in rows),passes=sum(x['exit_status']==0 for x in rows))))
