from pathlib import Path
import subprocess,json,lzma,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
names=['statement:pool_v1::verifier_registry::NHY_registry::entry_args_check','statement:pool_v1::verifier_registry::NHY_registry::entry_args_wrong_check']+['r1_pool_adapter::owned::NHY_auth::'+n for n in ['stage2_tail','stage2_tail_wrong','stage1_header','stage1_header_wrong','stage2_header','stage2_header_wrong','stage1_span','stage1_span_wrong','stage2_span','stage2_span_wrong']]
for i,n in enumerate(names,95):
 negative='_wrong' in n
 r=subprocess.run([sys.executable,str(E/'NHY_run.py'),f'NHY_K{i:03}','kani',n],capture_output=True,text=True)
 p=E/f'NHY_K{i:03}'/'receipt.json'
 if not p.exists():print(r.stdout[-1500:]);sys.exit(1)
 x=json.loads(p.read_text());print(i,n,x['exit_status'],x['wall_seconds'],flush=True)
 s=lzma.decompress((p.parent/'stdout.log.xz').read_bytes()).decode()
 if x['exit_status']!=(1 if negative else 0) or 'timed out' in s:print(r.stdout[-1500:]);sys.exit(1)
