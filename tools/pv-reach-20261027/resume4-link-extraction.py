import pathlib,subprocess,json,shlex
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume4'; pins=json.loads((E.parent/'extraction-pins.json').read_text())
script='''import pathlib,json,sys,hashlib
rows=json.load(sys.stdin);base=pathlib.Path('/home/dombarker/project-offloads');root=base/'codex-pv-reach-20261027/lean/objects';out=[]
for r in rows:
 rel=pathlib.Path(*r['module'].split('.'));src=base/'aspis-joint-20261019/sources'/rel.with_suffix('.lean');sha=hashlib.sha256(src.read_bytes()).hexdigest();assert sha==r['candidate_sha256'],(str(src),sha)
 p=base/'codex-cx-import-union-20261022/objects'/rel.with_suffix('.olean');assert p.is_file(),p
 dst=root/rel.with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
 for f in p.parent.glob(p.stem+'.*'):
  q=dst.parent/f.name
  if f.is_file() and not q.exists() and not q.is_symlink():q.symlink_to(f)
 out.append(dict(module=r['module'],source=str(src),source_sha256=sha,object=str(p),object_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source_freeze='evidence/pv-reach-20261027/extraction-pins.json',shared_source_written=False))
print(json.dumps(out,indent=2))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],input=json.dumps(pins),capture_output=True,text=True,check=True);(E/'extraction-verification.json').write_text(r.stdout);print('verified',len(json.loads(r.stdout)),'candidate source pins')
