from pathlib import Path
import json,subprocess,time,sys
E=Path(__file__).resolve().parent
while True:
 p=E/'KND_PAIRS.json'
 if p.exists() and len(json.loads(p.read_text()))==45:break
 time.sleep(30)
assert len(list(E.glob('KND_K*/receipt.json')))==90
subprocess.run([sys.executable,str(E/'KND_native.py')],check=True)
subprocess.run([sys.executable,str(E/'KND_audit.py')],check=True)
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
(E/'KND_STAGE2.md').write_text('Ninety Kani and five optimized native attempts are complete. KND_PAIRS.json and KND_PAIR_AUDIT.json retain matched-control results. Original-row scope limitations remain in KND_SCOPE.md. Every terminal run has a capped-host receipt and frozen graph validation.\n')
files=[p for p in E.rglob('*') if p.is_file() and '__pycache__' not in str(p) and p.suffix!='.lean' and p.name not in ['KND_LEAN_MANIFEST.json','KND_PREFLIGHT.json','KND_CHECK.json','KND_check.py','KND_after_kani.py','KND_PIPELINE.log']]
subprocess.run(['git','add',*[str(p) for p in files]],check=True)
subprocess.run(['git','commit','-m','Record concrete append transition checks'],check=True)
subprocess.run([sys.executable,str(E/'KND_check.py')],check=True)
subprocess.run([sys.executable,str(E/'KND_lean.py')],check=True)
print('ALL LEAN TARGETS TERMINAL',flush=True)
