from pathlib import Path
import subprocess,sys,json,lzma
E=Path(__file__).resolve().parent
for n,h in [(17,'NMO_terminal_reply_control'),(18,'NMO_terminal_argument_control'),(19,'NMO_terminal_footprint_control')]:
 a=f'NMO_K{n:03}';subprocess.run([sys.executable,str(E/'NMO_kconfig.py'),a,'r1_semantic::NMO_terminal::'+h],check=True)
 subprocess.run([sys.executable,str(E/'NMO_run.py'),a])
 p=E/a/'receipt.json';assert p.exists(),'Recover read-only; no new launch'
 r=json.loads(p.read_text());q=p.parent/'stdout.log';log=q.read_text()if q.exists()else lzma.decompress(q.with_name(q.name+'.xz').read_bytes()).decode()
 assert r['exit_status']==1 and 'VERIFICATION:- FAILED'in log and 'timed out'not in log,'Review verdict before any further scope'
 print(json.dumps({'attempt':a,'control':'expected failure'}),flush=True)
