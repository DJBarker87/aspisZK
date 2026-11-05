from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent

def run(i,control):
 env=dict(os.environ,NIG_CORE='1')
 if control:env.update(NIG_INVERT='1',NIG_NATIVE_CFG='NIG_corrupt')
 a=f'NIG_K{i:03}'
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'kani','NIG_filled::prefix_frame'],env=env)
 log=(E/a/'stdout.log').read_text()
 assert r.returncode==(1 if control else 0),(a,'exit')
 assert ('VERIFICATION:- FAILED' if control else 'VERIFICATION:- SUCCESSFUL')in log,(a,'verdict')
 assert 'timed out'not in log.lower()and'unwinding failures'not in log,(a,'unqualified')

# First control is byte-identical to the passing K044 source/configuration.
run(45,True)
rows=[dict(prefix_base=60,window_base=32,positive='NIG_K044',control='NIG_K045')]
i=46
for base in reversed(range(0,64,4)):
 for kbase in [0,32]:
  if base+3<kbase or (base,kbase)==(60,32):continue
  subprocess.run(['python3',str(E/'NIG_filled_window.py'),str(base),str(kbase)],check=True)
  run(i,False);run(i+1,True)
  rows.append(dict(prefix_base=base,window_base=kbase,positive=f'NIG_K{i:03}',control=f'NIG_K{i+1:03}'))
  (E/'NIG_FILLED_WINDOWS.json').write_text(json.dumps(rows,indent=2)+'\n')
  i+=2
assert i==92 and len(rows)==24
