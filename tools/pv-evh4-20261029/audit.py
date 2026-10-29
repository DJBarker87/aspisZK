"""Receipt/source audit only. No compiler, native binary, key or account action."""
from pathlib import Path
import ast,json,re,hashlib,subprocess
E=Path('evidence/pv-evh4-20261029');root=Path('/Users/dominic/ZK/.worktrees/pv-evh')
assert Path.cwd()==root
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/pv-evh-20261029'
sha=lambda b:hashlib.sha256(b).hexdigest()
for p in Path('tools/pv-evh4-20261029').glob('*.py'):ast.parse(p.read_text())
manifest=json.load(open(E/'scoped-manifest.json'));accepted={};runs=[]
for p in sorted(E.glob('receipt-*.json')):
 r=json.loads(p.read_text());assert 73600<=r['attempt']<=73699
 assert r['source_sha256']==sha(subprocess.check_output(['git','show',r['source_revision']+':'+r['source_path']]))
 assert r['exit'] is not None and r['wall'] is not None and r['peak_rss_kbytes'] is not None and r['swaps']=='0'
 assert r['admission']['allowed'] is True
 if r['accepted']:
  assert r['exit']=='0' and not any('sorryAx' in v for v in r['axioms'])
  accepted[r['target']]=r
 runs.append(r)
for m in manifest['modules']:
 source=Path(m['path']).read_bytes();assert sha(source)==m['source_sha256']==accepted[m['module']]['source_sha256']
 text=source.decode();assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option\s+(?:maxRecDepth|maxHeartbeats)',text)
 for n in m['theorems']:assert '#print axioms '+n in text or '#print axioms '+m['module']+'.'+n in text
# A source that actually failed elaboration is never submitted unchanged.
failed=set()
for r in runs:
 assert r['source_sha256'] not in failed,('unchanged failed source resubmission',r['attempt'])
 if not r['accepted']:failed.add(r['source_sha256'])
for q in E.rglob('*'):
 if q.is_file():assert q.stat().st_size<=20*1024*1024,q
paths=subprocess.check_output(['git','diff','--name-only','27b582ca44..HEAD'],text=True).splitlines()
assert not any(p.startswith(('crates/','programs/')) for p in paths)
assert all(not p.endswith('.lean') or p.startswith('lean/PV_EVH_') for p in paths)
summary=dict(branch='codex/pv-evh-20261029',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),lean_attempts=len(runs),accepted=len([r for r in runs if r['accepted']]),failed=len([r for r in runs if not r['accepted']]),native=0,kani=0,ids=[r['attempt'] for r in runs],refusals=[dict(path=str(p),epoch=json.loads(p.read_text())['epoch']) for p in sorted(E.glob('refusal-history-*.json'))],subprograms=manifest['modules'],axioms={r['target']:r['axioms'] for r in accepted.values()},full_prover_worldRun=False,opsNative_joint_success_witness=False,privacy_rows_removed=[],no_keys_or_accounts_used=True)
(E/'validation.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['refusals','subprograms','axioms']},indent=2))
