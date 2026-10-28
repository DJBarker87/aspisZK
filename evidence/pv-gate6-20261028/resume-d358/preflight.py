from pathlib import Path
import hashlib,json,time
R=Path(__file__).resolve().parent;H=R.parent
scanner=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py')
expected='662a42781e004635a4a0bde760a90082834834aa63bb15a3062ea0aef490542d'
actual=hashlib.sha256(scanner.read_bytes()).hexdigest();assert actual==expected,(actual,expected)
pins=json.loads((H/'timing-binary-pins.json').read_text());rows={}
for who,path in [('control',H/'combined/baseline/bin/prover_rw_gate'),('candidate',H/'bin/prover_rw_gate')]:
 actual=hashlib.sha256(path.read_bytes()).hexdigest();assert actual==pins[who]['sha256'],(who,actual)
 rows[who]=dict(path=str(path),sha256=actual,bytes=path.stat().st_size,matches=True)
(R/'preflight.json').write_text(json.dumps(dict(utc=time.time(),scanner_sha256=expected,binaries=rows,rebuild=False,stage_a_repeated=False),indent=2)+'\n')
