from pathlib import Path
import subprocess,sys,json,lzma
E=Path(__file__).resolve().parent
for n,h,expected,check in [(68,'copy_unit_real_caller',0,'VERIFICATION:- SUCCESSFUL'),(69,'copy_unit_unimplied',1,'assertion'),(70,'copy_unit_invert',1,'Failed Checks:'),(71,'copy_unit_modifies',1,'assignable')]:
 a=f'NHJ_K{n:03}';assert not (E/a).exists()
 r=subprocess.run([sys.executable,str(E/'NHJ_run.py'),a,'kani','r1_pool_adapter::owned::NHJ_owned::'+h],capture_output=True,text=True);(E/(a+'-controller.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise RuntimeError('Recover submitted job read-only; no resubmission')
 x=json.loads(p.read_text());s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode();ok=x['exit_status']==expected and check in s and 'timed out' not in s
 with (E/'NHJ_UNIT_MATRIX.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,expected=expected,exit=x['exit_status'],valid=ok))+'\n')
 print(a,ok,flush=True)
 if not ok:raise RuntimeError('Review interface shape before dependent use')
