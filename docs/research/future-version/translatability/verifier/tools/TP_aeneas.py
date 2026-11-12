#!/usr/bin/env python3
"""Aspis extraction probe: run Aeneas once on the LLBC of a Charon run. Runs INSIDE an fv_slot.sh scope.
Options are those of the PIN2 W8 runs. usage: XP_aeneas.py <charon-run> <aeneas-run> <second|first> <namespace> [noabort] [extra flags...]
`noabort` drops -abort-on-error so that one pass lists every function Aeneas rejects (a probe mode; R1's emissions used -abort-on-error)."""
import hashlib, json, subprocess, sys, time
from pathlib import Path
E = Path(__file__).resolve().parent
crun, arun, pair, ns = sys.argv[1:5]; rest = sys.argv[5:]
noabort = 'noabort' in rest; extra = [x for x in rest if x != 'noabort']
BIN = {'combined': ('/home/dombarker/project-offloads/codex-pv-combined-20261111/bin/aeneas', None), 'second': ('/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin/aeneas', '230ee9f0c4902ea3415a01960f6887e2d4c71bc82e8b4e78dfac398da657df91'),
       'first': ('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended', 'c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958')}[pair]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert BIN[1] is None or sha(BIN[0]) == BIN[1], 'tool hash mismatch'
llbc = E / 'runs' / crun / 'out.llbc'; assert llbc.is_file()
out = E / 'runs' / arun; out.mkdir(parents=True, exist_ok=False)
cmd = [BIN[0], '-diagnose-translation', '-sequential', '-no-progress-bar'] + ([] if noabort else ['-abort-on-error']) + extra + \
      ['-backend', 'lean', '-namespace', ns, '-dest', str(out / 'raw'), '-subdir', ns, '-split-files', str(llbc)]
(out / 'aeneas_command.json').write_text(json.dumps(dict(command=cmd, llbc_sha256=sha(llbc), charon_run=crun), indent=1) + '\n')
t0 = time.time()
with open(out / 'aeneas.log', 'w') as log:
    r = subprocess.run(['/usr/bin/time', '-v', '-o', str(out / 'aeneas.time')] + cmd, cwd=out, stdout=log, stderr=subprocess.STDOUT)
res = dict(run=arun, tool='aeneas', pair=pair, tool_sha256=sha(BIN[0]), exit=r.returncode, wall_seconds=round(time.time() - t0, 2), abort_on_error=not noabort)
for line in ((out / 'aeneas.time').read_text() if (out / 'aeneas.time').exists() else '').splitlines():
    if 'Maximum resident set size' in line: res['peak_rss_kib'] = int(line.split(':')[1])
res['outputs'] = {str(p.relative_to(out)): dict(sha256=sha(p), bytes=p.stat().st_size) for p in sorted((out / 'raw').rglob('*')) if p.is_file()} if (out / 'raw').exists() else {}
(out / 'aeneas_result.json').write_text(json.dumps(res, indent=1) + '\n')
print(json.dumps(res)); sys.exit(r.returncode)
