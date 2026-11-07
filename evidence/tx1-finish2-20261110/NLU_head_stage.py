from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
items=[(20,'NLU_Execute')]+[(21+i,'NLU_Head_'+name) for i,name in enumerate(json.loads((E/'NLU_HEAD_INPUT.json').read_text())['occurrences'])]
for n,module in items:
 a=f'NLU_L{n:03}'
 subprocess.run([sys.executable,str(E/'NLU_config.py'),a,module],check=True)
 if subprocess.run([sys.executable,str(E/'NLU_run.py'),a]).returncode:sys.exit(1)
