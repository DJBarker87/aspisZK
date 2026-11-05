from pathlib import Path
import subprocess,sys,json,lzma
E=Path(__file__).resolve().parent
for n,h,expected in [(84,'route_physical_two',0),(85,'route_physical_two_wrong',1),(86,'route_physical_zero',0),(87,'route_physical_zero_wrong',1)]:
 a=f'NHJ_K{n:03}';assert not (E/a).exists()
 r=subprocess.run([sys.executable,str(E/'NHJ_run.py'),a,'kani','r1_pool_adapter::owned::NHJ_owned::'+h],capture_output=True,text=True);(E/(a+'-controller.log')).write_text(r.stdout+r.stderr)
 f=E/a/'receipt.json'
 if not f.exists():raise RuntimeError('Recover read-only; no resubmission')
 x=json.loads(f.read_text());s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode();ok=x['exit_status']==expected and ('VERIFICATION:- FAILED' if expected else 'VERIFICATION:- SUCCESSFUL') in s and 'timed out' not in s and (not expected or 'Failed Checks: |r|*r' in s)
 print(a,ok,flush=True)
 if not ok:raise RuntimeError('Review before dependent use')
