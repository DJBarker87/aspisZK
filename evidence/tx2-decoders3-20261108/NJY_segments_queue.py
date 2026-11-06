from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for n,f,k in [(9,'entry','head'),(11,'entry','constructor'),(13,'entry','suffix'),(15,'entry','length'),(17,'registry','head'),(19,'registry','constructor'),(21,'registry','suffix'),(23,'registry','length')]:
 if not (E/f'NJY_K{n:03}'/'receipt.json').exists():subprocess.run([sys.executable,str(E/'NJY_segments.py'),f'NJY_K{n:03}',f,k,'positive'],check=True)
 if json.loads((E/f'NJY_K{n:03}'/'receipt.json').read_text())['exit_status']!=0:continue
 subprocess.run([sys.executable,str(E/'NJY_segments.py'),f'NJY_K{n+1:03}',f,k,'inverse'],check=True)
