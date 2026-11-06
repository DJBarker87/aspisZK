from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[]
for n,name in [(7,'add'),(9,'cache'),(11,'write')]:
 jobs += [(n,'NKJ_'+name+'_contract',[],0),(n+1,'NKJ_'+name+'_contract',['invert'],1)]
for n,name in [(13,'sums'),(15,'cache')]:jobs +=[(n,'NKJ_'+name+'_copy',[],0),(n+1,'NKJ_'+name+'_copy',['invert'],1)]
for n,name in [(17,'sums'),(22,'cache')]:
 jobs += [(n,'NKJ_'+name+'_weak_contract',[],0),(n+1,'NKJ_'+name+'_weak_contract',['invert'],1),(n+2,'NKJ_'+name+'_real_assert',[],0),(n+3,'NKJ_'+name+'_unimplied',[],1),(n+4,'NKJ_'+name+'_weak_contract',['modifies_bad'],1)]
for n,target,flags,expected in jobs:
 a=f'NKJ_K{n:03}'
 if len(sys.argv)>1 and n<int(sys.argv[1]):continue
 subprocess.run([sys.executable,str(E/'NKJ_kconfig.py'),a,'field::NKJ_segments::'+target,'kissat',*flags],check=True)
 r=subprocess.run([sys.executable,str(E/'NKJ_run.py'),a])
 rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 ok=(rc['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log) if expected==0 else (rc['exit_status']!=0 and 'VERIFICATION:- FAILED' in log and 'Failed Checks:' in log)
 with (E/'NKJ_QUEUE.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,expected_exit=expected,matched=ok))+'\n')
 if not ok:print(a+' unexpected; stop queue for review',flush=True);sys.exit(1)
