"""Isolated replays solely to replace missing per-harness RSS evidence from batch004."""
import pathlib,subprocess,sys
p=pathlib.Path(__file__).resolve().parent
for config in sys.argv[1:]:
 name=pathlib.Path(config).stem
 subprocess.run([sys.executable,str(p/'s2trust-reservation.py'),str(p/(name+'-reservation.json'))],check=True)
 r=subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64',sys.executable,str(p/'run_host.py'),config],cwd=p)
 if r.returncode: sys.exit(r.returncode)
