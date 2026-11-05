from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[('error_direct','NHC_error_direct.py',[])]+[(n,'NHC_vault_native.py',[n]) for n in ['array4','array8','array32','copt64_some','coptkey_some','copt64_bad','coptkey_bad','copt64_short','coptkey_short','mint_wronglen','token_wronglen','token_badstate','mint_uninit','mint_supply','mint_decimals','token_mint','token_authority','token_amount','token_flags','token_delegated_amount']]
index=78
for family,gen,args in jobs:
 for mode in ['positive','negative']:
  a=f'NHC_K{index:03}';index+=1
  r=subprocess.run([sys.executable,str(E/gen),*args,mode],capture_output=True,text=True)
  if r.returncode:print('generator error',family,r.stderr[-1000:]);sys.exit(2)
  harness='error::NHC_ErrorConversion::association' if family=='error_direct' else 'vault::NHC_Vault::association'
  r=subprocess.run([sys.executable,str(E/'NHC_kani_run.py'),a,harness],capture_output=True,text=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr)
  raw=(E/a/'stdout.log').read_text() if(E/a/'stdout.log').exists() else ''
  good=('VERIFICATION:- SUCCESSFUL' in raw) if mode=='positive' else ('VERIFICATION:- FAILED' in raw and 'Failed Checks:' in raw)
  timed='CBMC timed out.' in raw
  with(E/'NHC_TAIL_CAMPAIGN.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,family=family,mode=mode,exit=r.returncode,expected=good,timeout=timed))+'\n')
  print(a,family,mode,r.returncode,'expected',good,flush=True)
  if not good:
   print('Review before further launch',flush=True);sys.exit(3)
