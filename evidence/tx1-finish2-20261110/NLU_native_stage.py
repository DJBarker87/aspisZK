from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
names=['root_word','construct_owner','construct_claims','construct_alpha','construct_extra','construct_roots','construct_transcript','terminal_guard','circle_guard','arithmetic_arguments']
for k,name in enumerate(names):
 for bad,suffix in [(False,'cut'),(True,'control')]:
  n=5+2*k+int(bad);a=f'NLU_K{n:03}'
  subprocess.run([sys.executable,str(E/'NLU_kconfig.py'),a,'NLU_program::'+name+'_'+suffix],check=True)
  status=subprocess.run([sys.executable,str(E/'NLU_run.py'),a]).returncode
  log=(E/a/'stdout.log').read_text() if (E/a/'stdout.log').exists() else ''
  good=(status==1 and 'assertion failed: !selected' in log and 'VERIFICATION:- FAILED' in log) if bad else (status==0 and 'VERIFICATION:- SUCCESSFUL' in log)
  if not good:print('STOP pair '+a+'; isolate before any replacement',flush=True);sys.exit(1)
a='NLU_K025'
subprocess.run([sys.executable,str(E/'NLU_kconfig.py'),a,'NLU_program::constructor_family_codegen','codegen'],check=True)
sys.exit(subprocess.run([sys.executable,str(E/'NLU_run.py'),a]).returncode)
