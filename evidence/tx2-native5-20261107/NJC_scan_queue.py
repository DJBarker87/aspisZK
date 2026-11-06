from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[('NJC_K044','scan_s',True,1),('NJC_K045','scan_s_renamed',False,0),('NJC_K046','scan_k2',False,0),('NJC_K047','scan_k2',True,1),('NJC_K048','scan_k2_renamed',False,0),('NJC_K049','scan_query',False,0),('NJC_K050','scan_query',True,1),('NJC_K051','scan_query_renamed',False,0),('NJC_K052','scan_s_end',False,0),('NJC_K053','scan_s_end',True,1),('NJC_K054','scan_s_end_renamed',False,0),('NJC_K055','scan_query_end',False,0),('NJC_K056','scan_query_end',True,1),('NJC_K057','scan_query_end_renamed',False,0)]
for a,name,negative,expected in jobs:
 r=subprocess.run(['python3',str(E/'NJC_run.py'),a,'kani','verifier::candidate::NJC_scan::'+name],env={**os.environ,**({'NJC_INVERT':'1'} if negative else {})});assert r.returncode==expected,(a,r.returncode)
 s=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- '+('FAILED' if expected else 'SUCCESSFUL') in s and 'timed out' not in s
 print(a+' matched result',flush=True)
