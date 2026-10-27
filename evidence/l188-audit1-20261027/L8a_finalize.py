"""Validate retained audit receipts and source statements; clean own query outputs."""
from pathlib import Path
import json,hashlib,subprocess
import L8a_attempt as a
E=a.E
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for n in range(3,9):
 at=f'L8a_{n:03}';d=json.loads((E/at/'receipt.json').read_text())
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert d['swaps']=='0'
 for src,h in d['source_hashes'].items():
  p=E/at/'L8a_source.lean.txt' if n<=5 else E/(d['module']+'.lean')
  assert sha(p)==h,(at,p)
 text=(E/at/'stdout.log').read_text()
 if n>=6:
  assert d['exit_status']==0 and 'PANIC' not in text and 'error(' not in text
 if n==7:
  assert text.count('L8A_COMPLETE ')==1
 rows.append(dict(attempt=at,source_hash_valid=True,clean_query=(n>=6),exit=d['exit_status'],stdout_sha256=sha(E/at/'stdout.log')))
assert all(x['same_structured_kernel_statement'] for x in json.loads((E/'L8a_StatementComparison.json').read_text()))
for root in ['Rc10_Top','ARX_Root']:
 before=Path('evidence/replay-dry9-20261027/RPz8_'+root+'.kernel.txt').read_text()
 after=(E/('L8a_'+root+'.kernel.txt')).read_text()
 b=json.loads(before);c=json.loads(after)
 assert b['levelParamsRepr']==c['levelParamsRepr'] and b['typeRepr']==c['typeRepr']
 # Store one byte-identical canonical before/after pair for the complete kernel statement.
 for label,d in [('BEFORE',b),('AFTER',c)]:
  (E/f'L8a_{root}.{label}.statement.txt').write_text(json.dumps(d,sort_keys=True,separators=(',',':'))+'\n')
# Do not touch any shared cohort objects or live worker outputs.
payload='''from pathlib import Path
import json,hashlib,shutil
B=Path(%r);out=[]
for p in sorted((B/'L8a_objects').glob('*')):
 assert p.name.startswith('L8a_') and p.is_file() and not p.is_symlink(),p
 out.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
for row in out:Path(row['path']).unlink()
for name in ['L8a_check_layout','L8a_check_inputs']:
 p=B/name
 if p.exists():shutil.rmtree(p)
print(json.dumps(out,indent=2))
'''%a.B
r=a.ssh('python3 -',payload);assert r.returncode==0,r.stderr
(E/'L8a_cleanup.json').write_text(r.stdout)
# Check-only code: no compile run, unchanged package replay or Kani.
result=dict(receipts=rows,statement_kernel_expr_equal_to_RPz8=True,lean_invocations=6,clean_lean_passes=3,diagnostic_exit_zero_with_name_panics=1,elaboration_failures=2,preflight_only_ids=['L8a_001','L8a_002'],extraction_checks=1,Kani=0,reservation_retries=0,scope_policy='one at a time; 6G/8G/Swap0/Tasks64; -M7000',objects_removed=json.loads(r.stdout))
(E/'L8a_FinalVerification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
