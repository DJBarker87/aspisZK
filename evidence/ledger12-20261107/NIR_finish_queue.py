from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,group in enumerate(range(19,28),32):
 r=subprocess.run([sys.executable,str(E/'NIR_run.py'),f'NIR_L{i:03}','audit','batch'+str(group)])
 if r.returncode:
  # Retain verdict. Only the expressly known raw/summary discrepancy permits continuing other groups.
  log=(E/f'NIR_audit/batch{group}/proof{group}.log').read_text()
  if 'NHC_DecodeModel.decoder_error'in log and 'NEP_RESULT'in log:
   print(f'NIR L{i:03} retained audit failure; inspect raw roots under ab prime 3',flush=True)
  else:sys.exit(r.returncode)
