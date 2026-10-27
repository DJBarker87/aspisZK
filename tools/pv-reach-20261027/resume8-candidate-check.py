"""Verify source identity, full object fingerprints and literal environment for h6."""
import json,pathlib,subprocess,shlex
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume8'
script='''import pathlib,json,sys,hashlib,os
cs=json.load(sys.stdin);base=pathlib.Path('/home/dombarker/project-offloads');out={};origins={};env=json.load(open(base/'codex-pv-reach-20261027/lean/J.json'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
for m,ps in cs.items():
 out[m]=[]
 for s in ps:
  p=pathlib.Path(s);real=p.resolve();origin=real.relative_to(base).parts[0] if real.is_relative_to(base) else str(real);origins[origin]=origins.get(origin,0)+1
  # A lookup through a Stream B symlink does not authorize loading Stream A's object.
  stream_b=origin.startswith('codex-pv-')
  q=p.parent
  while q!=base and not (q/'J.json').exists():q=q.parent
  ej=q/'J.json';other=json.load(open(ej)) if ej.exists() else None
  out[m].append(dict(path=s,resolved_path=str(real),object_sha256=sha(p),origin=origin,stream_b_origin=stream_b,environment_path=str(ej) if other else None,toolchain_identical=bool(other and all(other.get(k)==env.get(k) for k in ['ELAN_TOOLCHAIN','LEAN','LEAN_GITHASH'])),lean_path_prefix_identical=bool(other and other.get('LEAN_PATH')==env.get('LEAN_PATH')),candidate_lean_path=other.get('LEAN_PATH') if other else None))
print(json.dumps(dict(origins=origins,candidates=out),indent=2))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],input=(E/'stream-b-candidate-objects.json').read_text(),capture_output=True,text=True,check=True)
(E/'candidate-identity-check.json').write_text(r.stdout)
d=json.loads(r.stdout);print('Origins',d['origins']);print('Stream B candidates',sum(x['stream_b_origin'] for v in d['candidates'].values() for x in v));print('Identical path',sum(x['lean_path_prefix_identical'] for v in d['candidates'].values() for x in v))
