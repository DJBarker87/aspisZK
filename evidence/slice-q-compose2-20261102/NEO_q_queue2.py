from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for n,name,control in [(29,'q_from_wide',False),(30,'q_from_wide',True),(31,'limbs_of',False),(32,'limbs_of',True),(33,'checked_q',False),(34,'checked_q',True)]:
 a=f'NEO_K{n:03}';subprocess.run([sys.executable,str(E/'NEO_kani.py'),a,'fast_pairing::canonical::NEO_q::'+name]+(['NEO_wrong_q'] if control else []))
 p=E/a/'receipt.json';assert p.exists(),'no terminal receipt; stop'
 d=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()
 assert d['exit_status']==int(control) and ('VERIFICATION:- FAILED' if control else 'VERIFICATION:- SUCCESSFUL') in log,'unexpected verdict; inspect'
 if control:assert '** 1 of ' in log,'wrong control failure'
