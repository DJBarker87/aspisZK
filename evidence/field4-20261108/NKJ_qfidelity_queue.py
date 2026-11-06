from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(56,'NKJ_return_contract',[],0),(57,'NKJ_return_contract',['invert'],1),(58,'NKJ_q_weak_contract',[],0),(59,'NKJ_q_weak_contract',['invert'],1),(60,'NKJ_q_real_assert',[],0),(61,'NKJ_q_unimplied',[],1),(62,'NKJ_q_weak_contract',['modifies_bad'],1),(63,'NKJ_q_copy',[],0),(64,'NKJ_q_copy',['invert'],1)]
for n,target,flags,expected in jobs:
 a=f'NKJ_K{n:03}'
 if len(sys.argv)>1 and n<int(sys.argv[1]):continue
 subprocess.run([sys.executable,str(E/'NKJ_kconfig.py'),a,'field::NKJ_segments::'+target,'kissat',*flags],check=True)
 r=subprocess.run([sys.executable,str(E/'NKJ_run.py'),a])
 rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 ok=(rc['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log) if expected==0 else (rc['exit_status']!=0 and 'VERIFICATION:- FAILED' in log and 'Failed Checks:' in log)
 with (E/'NKJ_QUEUE.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,expected_exit=expected,matched=ok))+'\n')
 if not ok:print(a+' unexpected; stop queue for review',flush=True);sys.exit(1)
