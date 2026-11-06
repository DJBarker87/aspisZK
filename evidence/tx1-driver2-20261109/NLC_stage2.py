from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for a,mod in [('NLC_L015','NLC_FrameAlgebra'),('NLC_L016','NLC_FinishTerminalMap'),('NLC_L017','NLC_FinishConstruct')]:
 subprocess.run([sys.executable,str(E/'NLC_config.py'),a,mod],check=True)
 r=subprocess.run([sys.executable,str(E/'NLC_run.py'),a])
 if r.returncode:sys.exit(r.returncode)
r=subprocess.run([sys.executable,str(E/'NLC_run.py'),'NLC_L014'])
if r.returncode:sys.exit(r.returncode)
for idx,name in enumerate(['map_cut','map_control','construct_cut','construct_control'],1):
 a=f'NLC_K{idx:03}';h='r1_semantic::NLC_native::'+name
 subprocess.run([sys.executable,str(E/'NLC_kconfig.py'),a,h],check=True)
 r=subprocess.run([sys.executable,str(E/'NLC_run.py'),a])
 # A negative control is expected to fail; inspect logs before classifying.
 if name.endswith('_cut') and r.returncode:sys.exit(r.returncode)
