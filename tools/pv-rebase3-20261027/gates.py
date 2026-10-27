"""Sequential task gates; refuse mismatches, preserve every refused admission."""
import json,pathlib,subprocess,sys,time
H=pathlib.Path(__file__).resolve().parent
mode=sys.argv[1]
def run(script,who,label,*args):
 for retry in range(11):
  name=label+(f'-retry{retry}' if retry else '')
  with (H/(name+'-launcher.log')).open('w') as log:
   status=subprocess.run(['python3',str(H/script),who,*args[:1],name,*args[1:]] if script=='build.py' else ['python3',str(H/script),who,name,*args],stdout=log,stderr=subprocess.STDOUT).returncode
  print(name,status,flush=True)
  if status==0:return
  out=H/who/name
  reservation=out/'reservation.json'
  if not (out/'receipt').exists() and reservation.exists() and json.loads(reservation.read_text()).get('admitted') is False:
   if retry<10:
    time.sleep(180);continue
  raise SystemExit(status)
if mode=='sbf':
 for m in ['default','devnet','pool']:run('build.py','candidate','build-'+m+'-gate',m)
elif mode=='native':
 run('native.py','candidate','build-devnet','cargo','build','--manifest-path','tools/r1-cost-probe/Cargo.toml','--release','--offline','--locked','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','devnet_spend')
elif mode=='fixture':
 for who in ['research','candidate']:
  run('native.py',who,'build-fixture','cargo','build','--release','--offline','--locked','-j','4','-p','aspis-r1-cost-probe','--example','prover_rw_gate','--features','optimized-terminal,r1p-check,ct-host-prover')
  run('native.py',who,'fixture-fixed',str(H/who/'bin/prover_rw_gate'),str(H/('fixtures-'+who)),'0','1')
 subprocess.run(['python3',str(H/'compare-fixtures.py')],check=True)
else:raise SystemExit('unknown gate')
