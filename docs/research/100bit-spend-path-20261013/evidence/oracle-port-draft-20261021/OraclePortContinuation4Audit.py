#!/usr/bin/env python3
"""Audit focused continuation-4 receipts without replaying unchanged Lean."""
import difflib,hashlib,json,pathlib,re,subprocess
root=pathlib.Path(__file__).resolve().parents[5]
ev=pathlib.Path(__file__).resolve().parent
base=root/'docs/research/100bit-spend-path-20261013'
baseline='c32df52af'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
git=lambda *a:subprocess.check_output(['git',*a],cwd=root,text=True)
modules=sorted(p.stem for p in (base/'lean').glob('OraclePort*C4.lean'))
manifest=json.loads((ev/'manifest.json').read_text())
attempts=[a for a in manifest['attempts'] if a['module'] in modules]
standard={'propext','Classical.choice','Quot.sound'}
final=[]
for name in modules:
 rows=[a for a in attempts if a['module']==name]
 assert rows, name
 last=rows[-1]
 assert last['exit']==0,(name,last['exit'])
 src=base/'lean'/f'{name}.lean'
 assert sha(src)==last['source_sha256'],name
 assert not git('ls-tree','--name-only',baseline,'--',str(src.relative_to(root))).strip(),name
 text=src.read_text()
 assert not re.search(r'(?<![\w.])(sorry|admit|native_decide|axiom)\b|set_option\s+(maxRecDepth|maxHeartbeats)', '\n'.join(l for l in text.splitlines() if not l.lstrip().startswith(('--','/-','*')))),name
 for theorem in re.findall(r'^theorem\s+(\w+)',text,re.M):
  assert f'#print axioms {theorem}' in text,(name,theorem)
 assert len(last['axioms'])==len(re.findall(r'^#print axioms ',text,re.M)),name
 for line in last['axioms']:
  if 'depends on axioms:' in line:
   used={a.strip() for a in line.split('[',1)[1].rsplit(']',1)[0].split(',')}
   assert used<=standard,(name,used)
 for dep in last['direct_imports']:
  assert pathlib.Path(dep['path']).exists() and sha(pathlib.Path(dep['path']))==dep['sha256'],(name,dep['module'])
 final.append(last)
for a in attempts:
 out=ev/f"{a['module']}-{a['attempt']}"
 assert json.loads((out/'receipt.json').read_text())==a
 assert sha(out/'source.lean')==a['source_sha256']
 assert all(k in a for k in ['source_revision','deps_fingerprint','exit','wall_seconds','peak_rss_bytes','swaps','axioms','errors'])
 assert '-M4400' in a['argv'] and '-j1' in a['argv'] and '-DElab.async=false' in a['argv']
 assert a['swaps']==0
 assert a['exit']==0 or a['errors']
for row in git('diff','--name-status',baseline,'--','docs/research/100bit-spend-path-20261013/lean').splitlines():
 status,path=row.split('\t',1)
 assert status=='A' and pathlib.Path(path).name.startswith('OraclePort'),row
layout=json.loads((ev/'OraclePortLayoutC4.json').read_text())
for path,pinned in layout['source_pins'].items(): assert sha(root/path)==pinned,path
endpoint='docs/research/100bit-spend-path-20261013/lean/R1FinalSoundnessBinPerQueryR19.lean'
before=git('show',baseline+':'+endpoint);after=(root/endpoint).read_text()
assert before==after
(ev/'OraclePortC4-headline-before.lean.txt').write_text(before)
(ev/'OraclePortC4-headline-after.lean.txt').write_text(after)
(ev/'OraclePortC4-existing-headline-signature.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='before',tofile='after')))
summary={'schema':'oracle-port-continuation4-focused-audit-v1','baseline':baseline,'audit_revision':git('log','-1','--format=%H','--',str((base/'lean').relative_to(root)),str((base/'design/OraclePortContinuation4-20261021.md').relative_to(root))).strip(),'audit_script_sha256':sha(pathlib.Path(__file__)),'modules':modules,'attempts':attempts,'final_attempts':[{'module':a['module'],'attempt':a['attempt'],'source_sha256':a['source_sha256'],'wall_seconds':a['wall_seconds'],'peak_rss_bytes':a['peak_rss_bytes'],'swaps':a['swaps'],'axiom_reports':len(a['axioms'])} for a in final],'successful_modules':len(final),'attempt_count':len(attempts),'failed_attempts':sum(a['exit']!=0 for a in attempts),'final_axiom_reports':sum(len(a['axioms']) for a in final),'peak_rss_bytes':max(a['peak_rss_bytes'] for a in attempts),'swaps':sum(a['swaps'] for a in attempts),'endpoint_sha256':sha(root/endpoint),'headline_premise_deletions':0,'completed_frozen_dV':False,'checked_acceptance_at_compiler_rows':'conditional ReaderBinding; candidate HCHECKS proved at byte-derived rows','release_claim':False,'full_frozen_manifest_replayed':False}
(ev/'OraclePortContinuation4Manifest.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['successful_modules','attempt_count','failed_attempts','final_axiom_reports','peak_rss_bytes','swaps','headline_premise_deletions']}))
