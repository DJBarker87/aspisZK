from pathlib import Path
import subprocess,json,lzma,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
for i,n in [(105,'stage1_span_wrong'),(106,'stage2_span'),(107,'stage2_span_wrong')]:
 r=subprocess.run([sys.executable,str(E/'NHY_run.py'),f'NHY_K{i:03}','kani','r1_pool_adapter::owned::NHY_auth::'+n],capture_output=True,text=True)
 p=E/f'NHY_K{i:03}'/'receipt.json'
 if not p.exists():print(r.stdout[-1500:]);sys.exit(1)
 x=json.loads(p.read_text());print(i,n,x['exit_status'],x['wall_seconds'],flush=True)
 s=lzma.decompress((p.parent/'stdout.log.xz').read_bytes()).decode()
 if x['exit_status']!=(1 if n.endswith('_wrong') else 0) or 'timed out' in s:print(r.stdout[-1500:]);sys.exit(1)
