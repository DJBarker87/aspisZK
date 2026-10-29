from pathlib import Path
import hashlib,json,sys
H=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1')
R=H.parents[1]/'codex-cx-prover-rw-20261023/src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if sys.argv[1]=='prepare':
 rows=[]
 for j,tag in enumerate(['caller-005','attempt-064','sampler-001']):
  a=R/f'translation-{tag}-audit.json';audit=json.loads(a.read_text());pre=R/f'receipts/aeneas-{tag}/preflight.json';x=json.loads(pre.read_text())
  
  inputs=[(k,v) for k,v in audit['inputs'].items() if k.endswith('.llbc')];assert len(inputs)==1
  _,pin=inputs[0];p=Path(pin['retained']);assert sha(p)==pin['sha256']
  expected={}
  for k,v in audit['artifacts'].items():
   if k.endswith('.lean'):
    q=R/x["target"][x["target"].index("-dest")+1]/k;assert sha(q)==v['sha256'],(q,sha(q),v)
    expected[q.name]=dict(path=str(q),sha256=sha(q),bytes=q.stat().st_size)
  assert {'Types.lean','Funs.lean'}<=expected.keys()
  for candidate,start in [('rebuild',73331),('backup',73334)]:
   binary=H/'aeneas/src/_build/default/main.exe' if candidate=='rebuild' else H.parents[1]/'codex-cx-prover-rw-20261023/rng-extractor/base/src/_build/default/main.exe'
   if candidate=='backup':assert sha(binary)=='562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19'
   n=start+j;dest=H/f'output-{n}';assert not dest.exists()
   cmd=x['target'].copy();cmd[0]=str(binary);cmd[cmd.index('-dest')+1]=str(dest);cmd[-1]=str(p)
   cfg=dict(command=cmd,cwd=str(H),candidate=candidate,tag=tag,binary_sha256=sha(binary),input_sha256=sha(p),expected=expected,historical_preflight_sha256=sha(pre),historical_audit_sha256=sha(a))
   (H/f'config-{n}.json').write_text(json.dumps(cfg,indent=2)+'\n');rows.append(cfg)
 (H/'identity-tests.json').write_text(json.dumps(rows,indent=2)+'\n')
else:
 n=int(sys.argv[1]);x=json.loads((H/f'config-{n}.json').read_text());r=json.loads((H/f'N{n}/receipt.json').read_text());rows=[]
 for name,pin in x['expected'].items():
  p=H/f'output-{n}'/name
  rows.append(dict(file=name,expected=pin['sha256'],actual=sha(p) if p.exists() else None,equal=p.exists() and sha(p)==pin['sha256']))
 out=dict(attempt=n,candidate=x['candidate'],tag=x['tag'],binary_sha256=x['binary_sha256'],exit_status=r['exit_status'],comparisons=rows,passed=r['exit_status']==0 and all(v['equal'] for v in rows))
 (H/f'N{n}/comparison.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
