import subprocess,sys
r=subprocess.run([sys.executable,'NIH_batch.py','scan'])
if r.returncode:sys.exit(r.returncode)
r=subprocess.run([sys.executable,'NIH_export.py']);sys.exit(r.returncode)
