#!/bin/bash
# Translatability pass, statement worker (T2). Run Aeneas once on the LLBC of a fv_tp2_charon.sh run,
# INSIDE an fv_slot.sh scope. Options as the probe's XP_aeneas.py (PIN2 W8 recipe).
# usage: fv_tp2_aeneas.sh <charon-run> <aeneas-run> <second|first> <namespace> [noabort] [extra flags...]
exec python3 - "$@" <<'PY'
import hashlib, json, subprocess, sys, time
from pathlib import Path
E = Path('/home/dombarker/project-offloads/future-version-20261111/tp2')
crun, arun, pair, ns = sys.argv[1:5]; rest = sys.argv[5:]
noabort = 'noabort' in rest; extra = [x for x in rest if x != 'noabort']
BIN = {'second': ('/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin/aeneas', '230ee9f0c4902ea3415a01960f6887e2d4c71bc82e8b4e78dfac398da657df91'),
       'first': ('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended', 'c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958')}[pair]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(BIN[0]) == BIN[1], 'tool hash mismatch'
llbc = E / 'runs' / crun / 'out.llbc'; assert llbc.is_file()
out = E / 'runs' / arun; out.mkdir(parents=True, exist_ok=False)
cmd = [BIN[0], '-diagnose-translation', '-sequential', '-no-progress-bar'] + ([] if noabort else ['-abort-on-error']) + extra + \
      ['-backend', 'lean', '-namespace', ns, '-dest', str(out / 'raw'), '-subdir', ns, '-split-files', str(llbc)]
(out / 'aeneas_command.json').write_text(json.dumps(dict(command=cmd, llbc_sha256=sha(llbc), charon_run=crun), indent=1) + '\n')
t0 = time.time()
with open(out / 'aeneas.log', 'w') as log:
    r = subprocess.run(['/usr/bin/time', '-v', '-o', str(out / 'aeneas.time')] + cmd, cwd=out, stdout=log, stderr=subprocess.STDOUT)
res = dict(run=arun, tool='aeneas', pair=pair, exit=r.returncode, wall_seconds=round(time.time() - t0, 2), abort_on_error=not noabort)
for line in ((out / 'aeneas.time').read_text() if (out / 'aeneas.time').exists() else '').splitlines():
    if 'Maximum resident set size' in line: res['peak_rss_kib'] = int(line.split(':')[1])
res['outputs'] = {str(p.relative_to(out)): dict(sha256=sha(p), bytes=p.stat().st_size) for p in sorted((out / 'raw').rglob('*')) if p.is_file()} if (out / 'raw').exists() else {}
(out / 'aeneas_result.json').write_text(json.dumps(res, indent=1) + '\n')
print(json.dumps(res)); sys.exit(r.returncode)
PY
