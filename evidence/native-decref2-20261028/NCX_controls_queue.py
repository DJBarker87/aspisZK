from pathlib import Path
import os,sys,subprocess,json
E=Path(__file__).resolve().parent
start=int(sys.argv[1]);shape=sys.argv[2]
for i,(target,control,expected) in enumerate([('contract','positive',0),('contract','ensures',1),('contract','modifies',1),('real','positive',0),('stub','positive',1)]):
 a=f'NCX_K{start+i:03}'
 name='NCX_unit_'+target if shape=='unit' else 'NCX_shape_'+target
 env=dict(os.environ,NCX_CONTROL=control)
 if shape!='unit':env['NCX_SHAPE']=shape
 r=subprocess.run([sys.executable,str(E/'NCX_kani.py'),a,'NCX_native::'+name],env=env,capture_output=True,text=True)
 print(a,r.stdout[-1100:]+r.stderr[-500:],flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 receipt=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
 assert receipt['exit_status']==expected and 'CBMC timed out' not in out and 'Checking harness NCX_native::'+name in out,(a,'unexpected control')
