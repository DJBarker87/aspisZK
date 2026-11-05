from pathlib import Path
import subprocess,sys,json,lzma
E=Path(__file__).resolve().parent
for n,h,check in [(73,'sdk_summary_max_drop_wrong','a.try_borrow_mut_data().is_ok()'),(74,'sdk_summary_max_argument_wrong','src as *const u8')]:
 a=f'NHJ_K{n:03}';assert not (E/a).exists()
 r=subprocess.run([sys.executable,str(E/'NHJ_run.py'),a,'kani','r1_pool_adapter::owned::NHJ_owned::'+h],capture_output=True,text=True);(E/(a+'-controller.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise RuntimeError('Recover read-only; no resubmission')
 x=json.loads(p.read_text());s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode();ok=x['exit_status']==1 and check in s and 'VERIFICATION:- FAILED' in s and 'timed out' not in s
 print(a,ok,flush=True)
 if not ok:raise RuntimeError('Control review required')
