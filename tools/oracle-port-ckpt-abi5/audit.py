#!/usr/bin/env python3
"""Receipt/scope audit. No compiler, solver, host job or release claim."""
import hashlib,json,re,subprocess,time
from pathlib import Path
R=Path(__file__).resolve().parents[2]; P=R/'docs/research/100bit-spend-path-20261013'; E=P/'evidence/ckpt-abi5-20261021'
BASE='30e4f18dbd541c5b2f9fa90afa9c1cab92fd21ba'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
start=time.monotonic()
subprocess.run(['python3','-B',str(R/'tools/oracle-port-ckpt-abi5/provenance.py'),'--check'],check=True)
m=json.loads((E/'manifest.json').read_text()); final={a['module']:a for a in m['attempts'] if a['final_current']}
modules=['OraclePortCkptAbi5'+x for x in ['Stage','Decision','Codec','Weights','Reached','Freeze']]
for name in modules:
 a=final[name];assert a['exit']==0 and a['swaps']==0
 source=P/'lean'/f'{name}.lean';assert sha(source)==a['source_sha256']
 out=E/f"{name}-{a['attempt']}"
 assert sha(out/'source.lean.txt')==sha(source)
 assert json.loads((out/'receipt.json').read_text())==a
 log=(out/'lean.log').read_text()
 assert 'sorryAx' not in log and not a['errors']
 for imported in a['direct_imports']:assert sha(Path(imported['path']))==imported['sha256']
 assert a['argv'][1:4]==['-j1','-M4400','-DElab.async=false']
 assert '/tmp/codex-cx-ckpt-abi5-20261021-objects' in a['lean_path']
 for line in a['axioms']:
  ax=re.search(r'depends on axioms: \[([\s\S]*?)\]',line)
  if ax:assert set(re.split(r',\s*',ax[1].strip())) <= {'propext','Classical.choice','Quot.sound'}
 text=source.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide|maxRecDepth|maxHeartbeats)\b|^\s*axiom\s',text)
 for theorem in re.findall(r'^theorem\s+(\w+)',text,re.M):
  assert '#print axioms '+theorem in text
  assert any('.'+theorem+"'" in line for line in a['axioms']),theorem
changes=subprocess.check_output(['git','diff','--name-only',BASE],cwd=R,text=True).splitlines()
for changed in changes:
 assert changed.startswith(('tools/oracle-port-ckpt-abi5/',str(E.relative_to(R))+'/')) or changed in [str((P/'lean'/f'{n}.lean').relative_to(R)) for n in modules] or changed==str((P/'design/CONE-AUDIT-20261021.md').relative_to(R)),changed
for name in modules:
 path=str((P/'lean'/f'{name}.lean').relative_to(R))
 assert subprocess.run(['git','cat-file','-e',BASE+':'+path],cwd=R,stderr=subprocess.DEVNULL).returncode != 0
assert all(p.stat().st_size<5_000_000 for p in E.rglob('*') if p.is_file())
assert not any(p.suffix in ['.olean','.ir','.so','.tar','.gz'] for p in E.rglob('*'))
result=dict(schema='checkpoint-abi5-audit-v1',exit=0,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 script_sha256=sha(Path(__file__)),wall_seconds=time.monotonic()-start,modules=modules,
 formal_attempts=len(m['attempts']),accepted=[{k:a[k] for k in ['module','attempt','source_sha256','exit','wall_seconds','peak_rss_bytes','swaps','source_revision','axioms']} for a in final.values()],
 complete_checkpoint_cone=False,accepted_run_join=False,headline_premises_removed=0,
 reuse='Pinned S10 kernel chronology and std model, pass-3 bounded Kani sections/writer/authentication and frozen2 predecessor evidence; no new Rust/ELF gate required.')
(E/'audit-result.json').write_text(json.dumps(result,indent=2)+'\n')
print('Receipt, standard-axiom, source-pin and scope audits pass; concrete checkpoint AcceptedRunJoin remains open')
