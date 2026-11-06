from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[('NJC_K006','k',True,1),('NJC_K007','k_renamed',False,0),('NJC_K008','e',False,0),('NJC_K009','e',True,1),('NJC_K010','e_renamed',False,0),('NJC_K011','raw4',False,0),('NJC_K012','raw4',True,1),('NJC_K013','raw4_renamed',False,0),('NJC_K014','raw16',False,0),('NJC_K015','raw16',True,1),('NJC_K016','raw16_renamed',False,0),('NJC_K017','raw32',False,0),('NJC_K018','raw32',True,1),('NJC_K019','raw32_renamed',False,0)]
for a,name,negative,expected in jobs:
 r=subprocess.run(['python3',str(E/'NJC_run.py'),a,'kani','verifier::NJC_readers::'+name],env={**os.environ,**({'NJC_INVERT':'1'} if negative else {})})
 receipt=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 assert r.returncode==expected,(a,r.returncode)
 assert ('VERIFICATION:- FAILED' in log or 'Status: FAILURE' in log or 'FAILURE' in log) if negative else ('VERIFICATION:- SUCCESSFUL' in log or 'VERIFICATION:- SUCCESSFUL' in log.replace(' ','' ) or 'successfully verified harnesses' in log),(a,'missing verdict')
 assert 'timed out' not in log and 'error: could not compile' not in log,(a,'not a matched semantic result')
 print(a+' matched '+('failing control' if negative else 'positive'),flush=True)
