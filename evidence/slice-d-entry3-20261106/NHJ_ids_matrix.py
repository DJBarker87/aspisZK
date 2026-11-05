from pathlib import Path
import subprocess,sys,json,lzma
E=Path(__file__).resolve().parent
for n,h,expected,check in [(44,'array_real_caller',0,'VERIFICATION:- SUCCESSFUL'),(45,'array_unimplied',1,'assertion'),(46,'array_invert',1,'Failed Checks:'),(47,'array_modifies',1,'assignable'),(48,'pool_devnet',0,'VERIFICATION:- SUCCESSFUL'),(49,'pool_devnet_wrong',1,'Failed Checks:'),(50,'registry_devnet',0,'VERIFICATION:- SUCCESSFUL'),(51,'registry_devnet_wrong',1,'Failed Checks:')]:
 a=f'NHJ_K{n:03}';assert not (E/a).exists()
 r=subprocess.run([sys.executable,str(E/'NHJ_run.py'),a,'kani','r1_pool_adapter::NHJ_ids::'+h],capture_output=True,text=True);(E/(a+'-controller.log')).write_text(r.stdout+r.stderr)
 f=E/a/'receipt.json'
 if not f.exists():raise RuntimeError('Recover submitted job read-only; never resubmit')
 x=json.loads(f.read_text());s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode();ok=x['exit_status']==expected and check in s and 'timed out' not in s
 with (E/'NHJ_IDS_MATRIX.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,expected=expected,exit=x['exit_status'],valid=ok))+'\n')
 print(a,ok,flush=True)
 if not ok:raise RuntimeError('Review before next dependent shape')
