from pathlib import Path
import subprocess,sys,time,json
D=Path(__file__).resolve().parent

def run(label,cmd):
 for attempt in range(11):
  out=D/(label+('' if not attempt else '-retry-%02d'%attempt))
  actual=[s.replace('{label}',out.name) for s in cmd]
  with (D/(out.name+'-driver.log')).open('w') as f:r=subprocess.run(actual,cwd=D,stdout=f,stderr=subprocess.STDOUT)
  print(label,attempt,r.returncode,flush=True)
  if r.returncode==0:return
  refused=False
  for n in ['reservation.json','admission-barrier.json']:
   p=out/n
   if p.exists() and not json.loads(p.read_text()).get('allowed',False):refused=True
  if not refused:raise SystemExit(r.returncode)
  if attempt==10:raise SystemExit('Ten reservation retries exhausted')
  time.sleep(180)
for mode in ['default','devnet','pool']:
 run('build-'+mode,['python3',str(D/'build.py'),'candidate',mode,'{label}'])
run('build-client',['python3',str(D/'native.py'),'{label}','cargo','build','--release','--offline','--locked','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','devnet_spend'])
run('build-fixture',['python3',str(D/'native.py'),'{label}','cargo','build','--release','--offline','--locked','-j','4','-p','aspis-r1-cost-probe','--example','prover_rw_gate','--features','optimized-terminal,r1p-check,ct-host-prover'])
run('fixture-fixed',['python3',str(D/'native.py'),'{label}',str(D/'bin/prover_rw_gate'),str(D/'fixtures-candidate'),'0','1'])
subprocess.run(['python3',str(D/'compare-fixtures.py')],check=True,stdout=open(D/'fixture-comparison-driver.log','w'),stderr=subprocess.STDOUT)
(D/'stage-a1-complete.json').write_text(json.dumps(dict(elf_pins=True,client=True,fixed_fixture=True,utc=time.time()),indent=2))
