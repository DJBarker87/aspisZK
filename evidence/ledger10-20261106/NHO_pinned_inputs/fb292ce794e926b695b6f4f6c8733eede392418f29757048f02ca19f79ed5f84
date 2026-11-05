from pathlib import Path
import sys,subprocess,json
E=Path(__file__).resolve().parent
for module in sys.argv[1:]:
 attempts=[json.loads(l) for l in (E/'NGU_ATTEMPTS.jsonl').read_text().splitlines()]
 n=max([int(x['attempt'][-3:]) for x in attempts if x['attempt'].startswith('NGU_L')]+[0])+1
 assert n<=80,'Lean budget exhausted'
 r=subprocess.run([sys.executable,str(E/'NGU_run.py'),f'NGU_L{n:03}','lean',module])
 if r.returncode:sys.exit(r.returncode)
