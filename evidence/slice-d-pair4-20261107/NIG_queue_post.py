from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for a,k,t,expected in [('NIG_K017','kani','weights::NIG_stages::KMX_checks::KMX_ptr_wrong',1),('NIG_K018','kani','weights::NIG_stages::KMX_checks::KMX_slice_wrong',1),('NIG_L004','lean','NIG_CommonPost',0),('NIG_L005','lean','NIG_LowPost',0)]:
 r=subprocess.run(['python3',str(E/'NIG_run.py'),a,k,t]);log=(E/a/'stdout.log').read_text()
 if r.returncode!=expected or 'timed out'in log.lower()or'unwinding failures'in log:raise SystemExit('Review '+a)
