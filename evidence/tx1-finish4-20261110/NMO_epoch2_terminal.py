"""Fresh bounded-view windows; stop on any unexpected verdict, never resubmit."""
from pathlib import Path
import subprocess,sys,json,lzma,hashlib,re
E=Path(__file__).resolve().parent
plan=json.loads((E/'NMO_EPOCH2_PLAN.json').read_text())
windows=json.loads((E/'NMO_TERMINAL_WINDOWS.json').read_text())
source=(E/'NMO_terminal.rs').read_bytes()
assert source==(E/plan['source_snapshot']).read_bytes(),'Freeze installed source first'
source_hash=hashlib.sha256(source).hexdigest()
for family in plan['terminal_order']:
 for role,suffix,bad in [(0,'',False),(1,'_reply_control',True),(2,'_argument_control',True),(3,'_footprint_control',True)]:
  if (E/'NMO_STOP_AFTER_SCOPE').exists():sys.exit(0)
  done=[json.loads(s)for s in (E/'NMO_EPOCH2_TERMINAL_VERDICTS.jsonl').read_text().splitlines()]if(E/'NMO_EPOCH2_TERMINAL_VERDICTS.jsonl').exists()else[]
  old=[x for x in done if x['family']==family and x['role']==role and x['source_sha256']==source_hash and x.get('classification')!='PRE_VERIFICATION_HARNESS_SELECTION_ERROR']
  if old:
   assert len(old)==1 and old[0]['expected_verdict'],'Recover/split the failed shape; do not resubmit'
   continue
  occupied={int(p.name[-3:])for p in E.glob('NMO_K[0-9][0-9][0-9]')if p.is_dir()}
  allocated=[json.loads(s)['id']for s in(E/'NMO_EPOCH2_ALLOCATIONS.jsonl').read_text().splitlines()]if(E/'NMO_EPOCH2_ALLOCATIONS.jsonl').exists()else[]
  ids=[i for i in plan['next_ids']if i not in occupied and i not in allocated]
  if not ids:
   print(json.dumps(dict(status='KANI_ID_BUDGET_EXHAUSTED',next_family=family,next_role=role,row_root=None)),flush=True);sys.exit(0)
  i=ids[0];a=f'NMO_K{i:03}';w=windows[family]
  short=('NMO_terminal' if family==0 and role else w['harness'])+suffix
  assert re.search(r'fn '+re.escape(short)+r'\s*\(',source.decode()),'Preflight exact harness exists'
  h='r1_semantic::NMO_terminal::'+short
  with(E/'NMO_EPOCH2_ALLOCATIONS.jsonl').open('a')as f:f.write(json.dumps(dict(id=i,attempt=a,family=family,role=role,source_sha256=source_hash))+'\n')
  subprocess.run([sys.executable,str(E/'NMO_kconfig.py'),a,h],check=True)
  subprocess.run([sys.executable,str(E/'NMO_run.py'),a])
  p=E/a/'receipt.json';assert p.exists(),'Recover read-only; never resubmit'
  d=json.loads(p.read_text());q=p.parent/'stdout.log';log=q.read_text()if q.exists()else lzma.decompress(q.with_name(q.name+'.xz').read_bytes()).decode()
  ok=d['exit_status']==int(bad)and('VERIFICATION:- FAILED'if bad else'VERIFICATION:- SUCCESSFUL')in log and'timed out'not in log
  row=dict(attempt=a,family=family,window=w,role=role,expected_verdict=ok,exit=d['exit_status'],timeout='timed out'in log,source_sha256=source_hash,epoch=2)
  with(E/'NMO_EPOCH2_TERMINAL_VERDICTS.jsonl').open('a')as f:f.write(json.dumps(row)+'\n')
  if not ok:sys.exit('Unexpected verdict: isolate/split before another dependent launch')
 print(json.dumps(dict(family=family,epoch=2,status='positive and three controls complete',row_root=None)),flush=True)
