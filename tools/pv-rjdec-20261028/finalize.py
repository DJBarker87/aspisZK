"""Collect original logs, verify accepted sources, and freeze bounded receipts."""
from pathlib import Path
import subprocess,json,hashlib,lzma,re,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjdec-20261028'
H='/home/dombarker/project-offloads/codex-pv-rjdec-20261028'
host='dombarker@100.108.41.90'
sha=lambda b:hashlib.sha256(b).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
accepted={v['module']:v for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted']}
checks=[];failed=[]
for p in sorted(E.glob('modules-*.json')):
 a=int(p.stem.split('-')[-1])
 for i,v in enumerate(json.loads(p.read_text())):
  for suffix in ['out','time']:
   subprocess.run(['scp','-q',f'{host}:{H}/evidence/{a}-{i:02d}.{suffix}',str(E/f'{a}-{i:02d}.{suffix}')],check=True)
  pin=v['source'];b=subprocess.check_output(['git','show',v['source_revision']+':'+pin['path']],cwd=R)
  assert sha(b)==v['source_sha256']
  if v['accepted']:
   assert (R/pin['path']).read_bytes()==b
   assert not any(t in ' '.join(v['axioms']) for t in ['sorryAx','Lean.ofReduceBool'])
  else:failed.append(dict(attempt=a,module=v['module'],source_revision=v['source_revision'],path=pin['path'],sha256=sha(b)))
  checks.append(dict(attempt=a,module=v['module'],accepted=v['accepted'],source_sha256=sha(b),source_revision=v['source_revision']))
for r in receipts:
 assert r['reservation']['allowed'] is True
 assert r['launch_admission']['allowed'] is True
 assert r['swaps']==0
 assert len(r['modules'])==1
 assert 61300<=r['attempt']<=61399
for a,revision in [(61307,'eb0aab683b'),(61311,'541ba510a0')]:
 d=E/f'native-{a}';tim=(d/f'time-native-{a}.log').read_text();ad=json.loads((d/f'admission-native-{a}.json').read_text());assert ad['allowed'] is True
 field=lambda pattern:re.search(pattern,tim)[1]
 x=json.loads((d/'result.json').read_text());profile=x['release']
 rec=dict(attempt=a,target=H+'/zeroize-probe/check.py',command=['systemd-run','--user','--scope','--quiet',f'--unit=rjdec-native-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',H+f'/evidence/time-native-{a}.log','python3',H+'/zeroize-probe/check.py'],exit=int(field(r'Exit status: (\d+)')),wall=field(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)'),peak_rss_kib=int(field(r'Maximum resident set size \(kbytes\): (\d+)')),swap=int(field(r'Swaps: (\d+)')),source_revision=subprocess.check_output(['git','rev-parse',revision],text=True,cwd=R).strip(),profile=profile,expected_phase='Compilation of the helper diagnostic, then finite value validation; no arithmetic elimination',resolved_feature_evidence=dict(client='../client-metadata.json.xz',probe='../native-feature-audit.json'),driver_source_sha256=sha(subprocess.check_output(['git','show',revision+':tools/pv-rjdec-20261028/zeroize-probe/check.py'],cwd=R)),toolchain=x['toolchain'],admission=ad,print_axioms='N/A native diagnostic; separate Lean certificate/model mismatch audit',result_sha256=sha((d/'result.json').read_bytes()),deployed_credit=False,note='61307 preliminary dependency resolution; 61311 all diagnostic dependency versions match deployed resolution. Source/LLVM diagnostic only, not full native correspondence.')
 assert rec['exit']==0 and rec['swap']==0
 (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
(E/'source-validation.json').write_text(json.dumps(checks,indent=2)+'\n')
(E/'retained-failed-sources.json').write_text(json.dumps(failed,indent=2)+'\n')
summary=dict(Lean_attempts=len(receipts),accepted=sum(r['accepted'] for r in receipts),rejected=sum(not r['accepted'] for r in receipts),native_scopes=2,Kani=0,void_attempts=0,axioms=[line for v in accepted.values() for line in v['axioms']],peak_Lean_RSS_bytes=max(r['peak_rss_bytes'] for r in receipts),swaps=0,stop='Checked deployed-helper source/IR counterexample to literal inherited compiler-fence schedule; requested native obligations OPEN; budget not exhausted.')
(E/'validation.json').write_text(json.dumps(summary,indent=2)+'\n')
for n in ['client-metadata.json','namespace-link-fix.json']:
 p=E/n
 if p.exists():
  b=p.read_bytes();(E/(n+'.xz')).write_bytes(lzma.compress(b));(E/(n+'.sha256')).write_text(sha(b)+'\n');p.unlink()
print(json.dumps({k:v for k,v in summary.items() if k!='axioms'}))
