from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(E/'NLC_run.py'),'NLC_L018'],check=True)
for idx,name in enumerate(['map_cut','map_control','construct_cut','construct_control'],2):
 a=f'NLC_K{idx:03}'
 subprocess.run([sys.executable,str(E/'NLC_kconfig.py'),a,'r1_semantic::NLC_native::'+name],check=True)
 r=subprocess.run([sys.executable,str(E/'NLC_run.py'),a])
 if name.endswith('_cut') and r.returncode:sys.exit(r.returncode)
