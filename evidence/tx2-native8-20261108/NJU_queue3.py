from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
for number,name,control in [(23,'round0_no_return',False),(24,'round0_no_return',True),(26,'round1_no_return',False),(27,'round1_no_return',True),(28,'final_no_return',False),(30,'final_no_return',True)]:
 env=os.environ.copy()
 if control:env['NJU_INVERT']='1'
 p=subprocess.run(['python3',str(E/'NJU_run.py'),f'NJU_K{number:03d}','kani','weights::NJU_finish::'+name],env=env)
 r=json.loads((E/f'NJU_K{number:03d}'/'receipt.json').read_text())
 if p.returncode!=1:raise SystemExit('Expected full Kani failure; inspect raw properties, never relabel a pass')
