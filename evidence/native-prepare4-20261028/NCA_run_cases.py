"""Own serial proof-case runner; admission/caps/backend remain in NCA_kani.py.
Never repeats a terminal attempt, including failed/timeout attempts.
"""
from pathlib import Path
import sys,subprocess,json,os
E=Path(__file__).resolve().parent
for spec in sys.argv[1:]:
    attempt,source,harness=spec.split(':',2)
    assert not (E/attempt/'receipt.json').exists(),attempt
    Path('/private/tmp/NCA_candidate.rs').write_bytes(Path(source).read_bytes())
    subprocess.run([sys.executable,str(E/'NCA_patch.py')],check=True)
    r=subprocess.run([sys.executable,str(E/'NCA_kani.py'),attempt,harness])
    if r.returncode:
        raise SystemExit('own wrapper failed; inspect before any further launch: '+attempt)

    if os.environ.get('NCA_STOP_ON_TIMEOUT')=='1' and 'timed out' in (E/attempt/'stdout.log').read_text():
        raise SystemExit('Stopped this same-shape case batch after timeout: '+attempt)
