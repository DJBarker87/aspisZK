from pathlib import Path
import os,sys,subprocess,json
E=Path(__file__).resolve().parent
start=int(sys.argv[1]);target=sys.argv[2]
for i in range(2):
 a=f'NCX_K{start+i:03}';env=dict(os.environ)
 if i:env['NCX_NEGATIVE']='1'
 r=subprocess.run([sys.executable,str(E/'NCX_kani.py'),a,'NCX_native::'+target],env=env,capture_output=True,text=True)
 print(a,r.stdout[-1400:]+r.stderr[-500:],flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 out=(E/a/'stdout.log').read_text();receipt=json.loads((E/a/'receipt.json').read_text())
 if 'CBMC timed out' in out:raise SystemExit('timed-out shape retired; no unchanged paired launch')
 if receipt['exit_status']!=i:raise SystemExit('unexpected pair result; review')
