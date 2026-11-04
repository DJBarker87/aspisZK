"""Check-only reproduction of both chains' transport and committed module text."""
from pathlib import Path
import json,hashlib,re,subprocess,lzma
E=Path(__file__).resolve().parent;R=E.parents[1];H=lambda b:hashlib.sha256(b).hexdigest()
def read(p):
 if p.exists():return p.read_bytes()
 if Path(str(p)+'.xz').exists():
  raw=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(raw)==Path(str(p)+'.sha256').read_text().strip();return raw
 return subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))],cwd=R)
report=[]
for folder,pre in [('slice-s-retarget2-20261104','NGE'),('slice-s-retarget3-20261104','NGF')]:
 D=E.parent/folder;p=json.loads(read(D/(pre+'_PROVENANCE.json')));graph=json.loads(read(D/(pre+'_SOURCE_GRAPH.json')));rename=p['namespace_map'];pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(rename,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
 for r in p['files']:
  src=graph[r['source_module']]['source'];assert H(src.encode())==r['source_sha256']
  frozen=read(R/r['source_path']);assert H(frozen)==r['source_sha256'],r['source_path']
  body='\n'.join(l for l in src.splitlines() if not l.startswith('import '))+'\n';assert body==r['before_body'] and H(body.encode())==r['original_body_sha256']
  after=pat.sub(lambda m:rename[m.group()],body)
  if pre=='NGF':after=after.replace('"NEX_Snapshot"','"NGF_NEX_Snapshot"')
  if ('open AspisR1TerminalDecoder' in body or 'Result AspisR1TerminalDecoder' in body) and 'core.result.Result.map_err' in body:after=re.sub(r'(?<![A-Za-z0-9_.])core.result.Result.map_err','AspisR1TerminalDecoder.core.result.Result.map_err',after)
  assert after==r['after_body'] and H(after.encode())==r['transformed_body_sha256']
  audit='''\nrun_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
'''
  target=read(D/(r['target_module']+'.lean'));assert target.decode()==''.join('import '+d+'\n' for d in r['imports_after'])+'\n'+after+audit
  report.append(dict(module=r['target_module'],source=r['source_path'],source_sha256=r['source_sha256'],target_sha256=H(target),body_transport_exact=True))
(E/'NGI_PROVENANCE_CHECK.json').write_text(json.dumps(dict(status='PASS',check_only=True,modules=report),indent=1)+'\n');print('PASS',len(report),'transported modules')
