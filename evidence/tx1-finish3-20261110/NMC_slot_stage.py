from pathlib import Path
import json,sys,subprocess
E=Path(__file__).resolve().parent
mods=json.loads((E/'NMC_SLOT_ORDER.json').read_text())[1:]
for n,module in enumerate(mods,29):
 a=f'NMC_L{n:03}'
 subprocess.run([sys.executable,str(E/'NMC_config.py'),a,module],check=True)
 if subprocess.run([sys.executable,str(E/'NMC_run.py'),a]).returncode:sys.exit('Fix this new module before the dependent chain')
