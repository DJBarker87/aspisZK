from pathlib import Path
import subprocess,sys,json
p=Path(__file__).parent
for name in sys.argv[1:]:
 r=subprocess.run([sys.executable,str(p/'compile.py'),'R1Z/PV_Inv_'+name],text=True,capture_output=True)
 t=json.loads((p/'TALLY.json').read_text());q=p/f"J{t['next_env_j_id']-1}";receipt=q/'receipt.json'
 if receipt.exists():
  d=json.loads(receipt.read_text());print(d['attempt'],name,d['exit'],d['wall'],d['peak_rss_kib'],flush=True)
 if r.returncode:
  print(r.stdout[-8000:]+r.stderr,flush=True);sys.exit(r.returncode)
