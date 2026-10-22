from pathlib import Path
import hashlib,json,difflib,subprocess
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
s=(L/'AspisR1SimControl21/Funs.lean').read_text().split('def transcript.control21.Transcript.queries\n',1)[1].split('\n/--',1)[0].split('  := do\n',1)[1]
pre,post=s.split('  let r ← PolicyInst.queries blocks15 blocks16\n',1)
actual=(L/'R1Z/ProverCommitQuery26.lean').read_text()
assert pre+'  ok (self1,blocks15,blocks16)' in actual
assert '  let r ← query blocks15 blocks16\n'+post in actual
rust=Path('crates/aspis-core/src/r0_transcript.rs').read_text()
body=rust.split('    fn scan(&mut self, block: &[u8; 32]) -> bool {',1)[1].split('\n    fn finish',1)[0]
assert '    fn scan(&mut self, block: &[u8; 32]) -> bool {'+body in (E/'harness/query26.rs').read_text()
rows=json.loads((E/'query-owners.json').read_text());D=E/'query-ports';D.mkdir(exist_ok=True)
for row in rows:
 raw=Path(row['original']).read_text();now=(L/(row['module']+'.lean')).read_text()
 row['promoted_sha256']=hashlib.sha256(now.encode()).hexdigest()
 (D/(row['module']+'.diff')).write_text(''.join(difflib.unified_diff(raw.splitlines(True),now.splitlines(True),fromfile='retained/'+row['module'],tofile='env-J/'+row['module'])))
(E/'query-owners.json').write_text(json.dumps(rows,indent=2)+'\n')
paths=[Path('crates/aspis-core/src/r0_transcript.rs'),Path('crates/aspis-r1-cost-probe/src/transcript.rs'),L/'AspisR1SimControl21/Funs.lean',L/'R1Z/ProverCommitQuery26.lean',E/'harness/query26.rs']
(E/'query-source-binding.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),checks=['exact source scan body retained','exact extracted materialization prefix','exact extracted trace suffix'],sha256={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},scope='Concrete policy/owned-source factorization plus separate library/control gates. Not a full shipped WholeRunJoin.'),indent=2)+'\n')
