import pathlib,json,subprocess,shlex,hashlib
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume5';host='dombarker@100.108.41.90'
manifest=json.loads((E/'external-object-manifest.json').read_text())
script='''import pathlib,json,sys,hashlib
rows=json.load(sys.stdin);e=json.load(open('/home/dombarker/project-offloads/codex-pv-reach-20261027/lean/J.json'));roots=[pathlib.Path(x) for x in e['LEAN_PATH'].split(':')];bad=[]
for r in rows:
 rel=pathlib.Path(r['module']).with_suffix('.olean');p=next((x/rel for x in roots if (x/rel).is_file()),None);sha=hashlib.sha256(p.read_bytes()).hexdigest() if p else None
 if sha!=r['object_sha256']:bad.append(dict(module=r['module'],path=str(p),expected=r['object_sha256'],actual=sha))
print(json.dumps(dict(checked=len(rows),mismatches=bad)))
'''
r=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(script)],input=json.dumps(manifest),text=True,capture_output=True,check=True);(E/'effective-h4.json').write_text(r.stdout);print(r.stdout);assert not json.loads(r.stdout)['mismatches']
script='''import pathlib,json,re
base=pathlib.Path('/home/dombarker/project-offloads');hits=[]
for p in base.glob('codex-pv-*/**/*'):
 if p.is_file() and (p.name.startswith(('receipt-','used-','pvre-out-','pvre-time-','out-','time-'))):
  ids=re.findall(r'(?<![0-9])(373[0-9]{2})(?![0-9])',p.name)
  if ids:hits.append(dict(path=str(p),ids=list(map(int,ids))))
sent=base/'r1-privacy-build-integration-20261019/sent.txt'
lines=[x for x in sent.read_text().splitlines() if re.search(r'(?<![0-9])373[0-9]{2}(?![0-9])',x)] if sent.is_file() else []
print(json.dumps(dict(hits=hits,sent=lines)))
'''
r=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(script)],capture_output=True,text=True,check=True);d=json.loads(r.stdout);(E/'cross-job-id-check.json').write_text(json.dumps(d,indent=2)+'\n');used={i for r in d['hits'] for i in r['ids']};print('used',sorted(used));assert not used.intersection(range(37335,37400))
