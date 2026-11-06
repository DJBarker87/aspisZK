from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
for number,name,control in [(18,'round0_window',True),(19,'round1_window',False),(20,'round1_window',True),(21,'final_window',False),(22,'final_window',True)]:
 env=os.environ.copy()
 if control:env['NJU_INVERT']='1'
 p=subprocess.run(['python3',str(E/'NJU_run.py'),f'NJU_K{number:03d}','kani','weights::NJU_finish::'+name],env=env)
 r=json.loads((E/f'NJU_K{number:03d}'/'receipt.json').read_text())
 if p.returncode not in ([1,10] if control else [0]):raise SystemExit('Inspect unexpected result before continuing')
