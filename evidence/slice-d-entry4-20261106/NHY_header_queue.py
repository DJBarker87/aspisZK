from pathlib import Path
import json,subprocess,sys,lzma
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
names=['registry_v2_header_wrong','entry_v2_header','entry_v2_header_wrong','registry_v1_header','registry_v1_header_wrong','entry_v1_header','entry_v1_header_wrong']
for i,n in enumerate(names,58):
 r=subprocess.run([sys.executable,str(E/'NHY_run.py'),f'NHY_K{i:03}','kani','statement:pool_v1::verifier_registry::NHY_registry::'+n+'_check'],capture_output=True,text=True)
 p=E/f'NHY_K{i:03}'/'receipt.json'
 if not p.exists():print(r.stdout[-1500:]);sys.exit(1)
 x=json.loads(p.read_text());print(i,n,x['exit_status'],x['wall_seconds'],flush=True)
 s=lzma.decompress((p.parent/'stdout.log.xz').read_bytes()).decode()
 if x['exit_status']!=(1 if n.endswith('_wrong') else 0) or 'timed out' in s:print(r.stdout[-1500:]);sys.exit(1)
