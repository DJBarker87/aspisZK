from pathlib import Path
import subprocess,json,lzma,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
names=[('r1_pool_adapter::owned::NHY_auth::pda_reply',False),('r1_pool_adapter::owned::NHY_auth::pda_reply_wrong',True)]+[('statement:pool_v1::verifier_registry::NHY_registry::'+n+'_check',n.endswith('_wrong')) for n in ['registry_v1_header_wrong','entry_v1_header','entry_v1_header_wrong','entry_record','entry_record_wrong','registry_args','registry_args_wrong','entry_args','entry_args_wrong']]
for i,(n,negative) in enumerate(names,87):
 r=subprocess.run([sys.executable,str(E/'NHY_run.py'),f'NHY_K{i:03}','kani',n],capture_output=True,text=True)
 p=E/f'NHY_K{i:03}'/'receipt.json'
 if not p.exists():print(r.stdout[-1500:]);sys.exit(1)
 x=json.loads(p.read_text());print(i,n,x['exit_status'],x['wall_seconds'],flush=True)
 s=lzma.decompress((p.parent/'stdout.log.xz').read_bytes()).decode()
 if x['exit_status']!=(1 if negative else 0) or 'timed out' in s:print(r.stdout[-1500:]);sys.exit(1)
