from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
modules=['XRq_SamplerInterface','XRq_OrdinaryScalar','XRq_FromQm','XRq_GammaDecode','XRq_GammaAssociation','XRq_AddValue','XRq_ScalarSub','XRq_ComplexSub','XRq_QmSub','XRq_ScalarK','XRq_GammaScalar','XRq_LeafErrors','XRq_ByteInspect','XRq_Nonvacuity']
for i,m in enumerate(modules,65):
 a=f'XRq_L{i:03}'
 if (E/a/'receipt.json').exists():continue
 r=subprocess.run([sys.executable,str(E/'XRq_attempt.py'),a,str(E/(m+'.lean')),m],capture_output=True,text=True)
 print(a,m,r.stdout[-9000:],r.stderr[-300:],flush=True)
 if r.returncode or not (E/a/'receipt.json').exists() or json.loads((E/a/'receipt.json').read_text())['exit_status']!=0:raise SystemExit('STOP new proof')
