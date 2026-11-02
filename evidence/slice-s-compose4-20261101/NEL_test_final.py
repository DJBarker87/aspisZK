from pathlib import Path
import subprocess,time,json,hashlib
E=Path(__file__).resolve().parent
names=['NEL_validate.py','NEL_tests.py','NEL_LEDGER_DELTA.json','NEL_REVIEWED_CERTIFICATES.json']
pins={n:hashlib.sha256((E/n).read_bytes()).hexdigest() for n in names}
t=time.monotonic()
with (E/'NEL_TESTS_FINAL.log').open('w') as f:r=subprocess.run(['python3',str(E/'NEL_tests.py')],stdout=f,stderr=subprocess.STDOUT)
assert pins=={n:hashlib.sha256((E/n).read_bytes()).hexdigest() for n in names}
(E/'NEL_TESTS_FINAL.json').write_text(json.dumps(dict(command=['python3',str(E/'NEL_tests.py')],exit=r.returncode,wall_seconds=time.monotonic()-t,source_sha256=pins,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),reason='Distinct final log after overlapping earlier local test runs wrote a shared log; missing unambiguous success artifact repaired. No compiler/prover replay.'),indent=1)+'\n')
raise SystemExit(r.returncode)
