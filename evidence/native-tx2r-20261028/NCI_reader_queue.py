from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
jobs=[(3,'raw1_wrong'),(4,'raw4_ok'),(5,'raw4_wrong'),(6,'raw16_ok'),(7,'raw16_wrong'),(8,'raw32_ok'),(9,'raw32_wrong')]
for i,h in jobs:
 a=f'NCI_K{i:03}'
 r=subprocess.run(['python3',str(E/'NCI_kani.py'),a,'crates/aspis-r1-cost-probe','verifier::NCI_reader::'+h,str(E/'NCI_reader.patch')],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr);print(a,r.stdout[-1600:],r.stderr[-500:],flush=True)
 if r.returncode:raise SystemExit('runner failure')
 rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
 if 'VERIFICATION:- FAILED' not in out if h.endswith('wrong') else 'VERIFICATION:- SUCCESSFUL' not in out:
  raise SystemExit('unexpected verdict; inspect, do not rerun')
