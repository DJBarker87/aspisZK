from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for item in sys.argv[1:]:
 a,name=item.split(':',1)
 r=subprocess.run([sys.executable,str(E/'NCH_kani.py'),'NCH_K'+a,'verifier::candidate::NCH_candidate::'+name])
 if r.returncode:raise SystemExit(r.returncode)
 receipt=json.loads((E/("NCH_K"+a)/"receipt.json").read_text())
 log=(E/("NCH_K"+a)/"stdout.log").read_text()
 if "timed out" in log.lower() or receipt["exit_status"] in [124,137]:
  raise SystemExit("STOP queue at timeout/kill; isolate and split before next launch")

