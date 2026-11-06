from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for i,name in enumerate(json.loads((E/'NLU_HEAD_INPUT.json').read_text())['occurrences']):
 n=21+i
 if n<23:continue
 a=f'NLU_L{n:03}';subprocess.run([sys.executable,str(E/'NLU_config.py'),a,'NLU_Head_'+name],check=True)
 if subprocess.run([sys.executable,str(E/'NLU_run.py'),a]).returncode:sys.exit(1)
