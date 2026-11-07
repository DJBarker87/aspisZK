from pathlib import Path
import json,subprocess,sys,lzma
E=Path(__file__).resolve().parent;family=int(sys.argv[1]);w=json.loads((E/'NMO_TERMINAL_WINDOWS.json').read_text())[family];assert 1<=family<19
assert (E/'NMO_terminal.rs').read_bytes()==(E/'NMO_L043/sources/NMO_terminal.rs').read_bytes(),'Freeze native source before window families'
for role,suffix,bad in [(0,'',False),(1,'_reply_control',True),(2,'_argument_control',True),(3,'_footprint_control',True)]:
 if (E/'NMO_STOP_AFTER_SCOPE').exists():sys.exit(0)
 a=f'NMO_K{16+4*family+role:03}';h='r1_semantic::NMO_terminal::'+w['harness']+suffix
 subprocess.run([sys.executable,str(E/'NMO_kconfig.py'),a,h],check=True);subprocess.run([sys.executable,str(E/'NMO_run.py'),a])
 p=E/a/'receipt.json';assert p.exists(),'Recover read-only; no further launch'
 x=json.loads(p.read_text());q=p.parent/'stdout.log';log=q.read_text()if q.exists()else lzma.decompress(q.with_name(q.name+'.xz').read_bytes()).decode()
 ok=x['exit_status']==int(bad)and('VERIFICATION:- FAILED'if bad else'VERIFICATION:- SUCCESSFUL')in log and'timed out'not in log
 with(E/'NMO_WINDOW_VERDICTS.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,family=family,window=w,role=role,expected_verdict=ok,exit=x['exit_status'],timeout='timed out'in log))+'\n')
 if not ok:sys.exit('Unexpected verdict; isolate/split this window before another dependent launch')
print(json.dumps(dict(family=family,status='positive and three controls complete')),flush=True)
