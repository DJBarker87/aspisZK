import subprocess,sys
for mode in ['fixtures','scan']:
 subprocess.run([sys.executable,'NKR_batch.py',mode,sys.argv[1]],check=True)
