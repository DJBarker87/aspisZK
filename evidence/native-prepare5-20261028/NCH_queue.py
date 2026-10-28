from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for item in sys.argv[1:]:
 a,name=item.split(':',1)
 r=subprocess.run([sys.executable,str(E/'NCH_kani.py'),'NCH_K'+a,'verifier::candidate::NCH_candidate::'+name])
 if r.returncode:raise SystemExit(r.returncode)
 receipt=json.loads((E/("NCH_K"+a)/"receipt.json").read_text())
 log=(E/("NCH_K"+a)/"stdout.log").read_text()
 if "internal compiler error" in log.lower() or "could not compile" in log.lower():
  raise SystemExit("STOP queue at compiler failure; repair own harness or move to an independent shape")
 if "timed out" in log.lower() or receipt["exit_status"] in [124,137]:
  raise SystemExit("STOP queue at timeout/kill; isolate and split before next launch")

