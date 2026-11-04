from pathlib import Path
import subprocess,sys,json,time
E=Path(__file__).resolve().parent
roots=json.loads((E/'NFM_AUDIT_ROOTS.json').read_text());assert len(roots['groups'])==33
start=time.monotonic()
for index,group in enumerate(roots['groups']):
 a=f'NFM_L{28+index:03}'
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFM_run.py'),a,'auditbin',f'proof{index}'],stdout=out,stderr=subprocess.STDOUT)
 print(a,index,len(group),r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
 receipt=json.loads((E/a/'receipt.json').read_text())
 with (E/'NFM_AUDIT_PROGRESS.jsonl').open('a') as out:out.write(json.dumps(dict(attempt=a,roots=group,wall_seconds=receipt['wall_seconds'],peak_rss_kib=receipt['peak_rss_kib'],swaps=receipt['swaps'],elapsed_seconds=time.monotonic()-start))+'\n')
