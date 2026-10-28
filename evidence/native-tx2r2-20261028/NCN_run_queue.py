from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
# Explicit queue file; serial and stop on timeout/codegen/unexpected verdict.
for job in json.loads(Path(sys.argv[1]).read_text()):
 a=job['attempt'];h=job['harness'];patch=E/job['patch']
 assert not (E/a/'receipt.json').exists(),'never rerun a submitted receipt'
 r=subprocess.run(['python3',str(E/'NCN_kani.py'),a,'crates/aspis-r1-cost-probe',h,str(patch)],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr);print(a,r.stdout[-1100:],r.stderr[-500:],flush=True)
 if r.returncode:raise SystemExit('runner failure')
 rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
 if 'timed out' in out or 'could not compile' in out:raise SystemExit('timeout/codegen; isolate before a new submission')
 expected='VERIFICATION:- FAILED' if job['negative'] else 'VERIFICATION:- SUCCESSFUL'
 assert expected in out,'unexpected verdict'
