from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
pairs=['terminal_guard','circle_guard','low','high','blind','extra28','state_before','decode25']
queue=[(22+2*n+int(bad),name,bad)for n,name in enumerate(pairs)for bad in [False,True]]+[(38,'decode26',False),(39,'terminal_entry',False),(40,'terminal_entry',True)]
for n,name,bad in queue:
 a=f'NMC_K{n:03}';h='NMC_program::'+name+('_control'if bad else'_cut')
 subprocess.run([sys.executable,str(E/'NMC_kconfig.py'),a,h],check=True)
 subprocess.run([sys.executable,str(E/'NMC_run.py'),a])
 p=E/a/'receipt.json';assert p.exists(),'Recover read-only, never resubmit'
 x=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()
 timeout='timed out'in log or x['exit_status']==124
 expected=x['exit_status']==(1 if bad else 0)and not timeout
 with(E/'NMC_NATIVE_VERDICTS.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,harness=h,expected_verdict=expected,timeout=timeout,exit_status=x['exit_status']))+'\n')
 if not expected:sys.exit('Review isolated member before continuing independent members')
