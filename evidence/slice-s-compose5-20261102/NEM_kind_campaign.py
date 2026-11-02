from pathlib import Path
import subprocess,sys,json,re
E=Path(__file__).resolve().parent
jobs=[(102,'statement','positive',0),(103,'statement','wrong_value',1),(104,'payment','positive',0),(105,'payment','wrong_value',1),(106,'parse','positive',0),(107,'parse','wrong_value',1),(108,'statement','wrong_receiver',1),(109,'statement','wrong_place',1),(110,'parse','wrong_place',1)]
for n,case,mode,want in jobs:
 a=f'NEM_K{n:03}'
 if n<104:continue # completed receipts retained; no resubmission
 assert not (E/a).exists()
 subprocess.run([sys.executable,str(E/'NEM_prepare_kind.py'),case,mode],check=True)
 for p in E.glob('NEM_*CURRENT.json'):
  if re.fullmatch(r'NEM_[A-Z_]+CURRENT\.json',p.name):(E/(a+'-'+p.name)).write_bytes(p.read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEM_kani_run.py'),a,'kani','pool_v1::pair_forest_terminal::NEM_kind_call::kind_call'])
 log=(E/a/'stdout.log').read_text()
 assert r.returncode==want and ('VERIFICATION:- SUCCESSFUL' if want==0 else 'VERIFICATION:- FAILED') in log,(a,r.returncode)
