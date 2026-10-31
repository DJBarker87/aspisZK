from pathlib import Path
import os,sys,subprocess,json
E=Path(__file__).resolve().parent;num=int(sys.argv[1])
plans=[('shape_contract',{}),('shape_contract',dict(NEC_FIDELITY_INVERT='1')),('shape_client',{}),('shape_client',dict(NEC_FIDELITY_STUB='1')),('shape_contract',dict(NEC_FIDELITY_BAD_MODIFIES='1')),('shape_client',dict(NEC_FIDELITY_CLIENT_INVERT='1'))]
for target,settings in plans:
 env={k:v for k,v in os.environ.items() if not k.startswith('NEC_')};env.update(NEC_PROGRAM='1',NEC_PROGRAM_FIDELITY='1');env.update(settings)
 a=f'NEC_K{num:03d}';num+=1
 r=subprocess.run([sys.executable,str(E/'NEC_run.py'),a,'kani','r1_pool_adapter::NEC_program_fidelity::'+target],env=env,capture_output=True,text=True)
 if r.returncode:print(r.stdout[-1000:]+r.stderr[-1000:],flush=True);raise SystemExit(r.returncode)
 receipt=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 summary=dict(attempt=a,target=target,settings=settings,exit_status=receipt['exit_status'],compiler_rejection=('error[E' in log or 'error: could not compile' in log),timeout='CBMC timed out' in log)
 with (E/'NEC_PROGRAM_FIDELITY.jsonl').open('a') as f:f.write(json.dumps(summary)+'\n')
 print(json.dumps(summary),flush=True)
 if 'CBMC timed out' in log:break
 if 'error[E' in log and not settings.get('NEC_FIDELITY_STUB'):raise SystemExit('Unexpected own input/compiler error; repair first')
print('next attempt',num,flush=True)
