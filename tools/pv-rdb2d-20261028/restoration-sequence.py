from pathlib import Path
import subprocess,sys,time,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2d-20261028'
while not (E/'lean-61060/receipt.json').exists():time.sleep(5)
assert json.loads((E/'lean-61060/receipt.json').read_text())['exit']==0
args=[f'{n}:{m}'for n,m in zip(range(61061,61068),['DivisionRestoration','DivisionLoop','DigitsRestoration','LowRestoration','CarryRestoration','CarryLoop','GammaRestoration'])]
sys.exit(subprocess.run([sys.executable,str(R/'tools/pv-rdb2d-20261028/run-sequence.py'),*args]).returncode)
