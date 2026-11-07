from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
scan=json.loads((E/'NMG_audit/scan/result.json').read_text());assert scan['exit_status']==0 and scan['raw_standard_only'] is True
for i in range(76):
 a='NMG_L'+str(25+i).zfill(3);mode='proof'+str(i)
 r=subprocess.run([sys.executable,str(E/'NMG_run.py'),a,mode])
 p=E/a/'receipt.json'
 if not p.exists():raise RuntimeError('No scope receipt; STOP queue, recover read-only if submitted: '+a)
 result=E/'NMG_audit'/mode/'result.json';data=json.loads(result.read_text()) if result.exists() else None
 with (E/'NMG_QUEUE.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,mode=mode,exit=r.returncode,raw_standard_only=data.get('raw_standard_only') if data else None,has_result=data is not None))+'\n')
 if r.returncode not in [0,1,124,137]:raise RuntimeError('Unexpected scope error; STOP '+a)
print('NMG queue exhausted100 numbered slots')
