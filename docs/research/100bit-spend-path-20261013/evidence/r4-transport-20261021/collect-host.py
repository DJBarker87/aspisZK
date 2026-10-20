#!/usr/bin/env python3
"""Normalize focused host attempts without rerunning any gate."""
from pathlib import Path
import json,hashlib,re
here=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
source=json.loads((here/'source-inventory.json').read_text())
tools=sha(here/'toolchain.json')
rows=[]
for d in sorted((here/'host-receipts').iterdir()):
 if not d.is_dir() or not (d/'receipt.json').exists():continue
 r=json.loads((d/'receipt.json').read_text())
 wide=d.name.startswith('wide-')
 sourcefile='crates/aspis-r1-cost-probe/src/sampler.rs' if wide else 'crates/aspis-core/src/r0_transcript.rs'
 log=(d/'stdout.log').read_text(); err=(d/'stderr.log').read_text()
 rows.append(dict(attempt=d.name,module=r['command'],source_revision=r['source_revision'],source_sha256=source['files'][sourcefile]['sha256'],
  deps_fingerprint=hashlib.sha256((tools+sha(here/('wide-source-cut.json' if wide else 'scanner-source-cut.json'))).encode()).hexdigest(),
  exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],
  cgroup_memory_peak_bytes=r['cgroup_memory_peak_bytes'],limits=r['limits'],
  print_axioms=r['print_axioms'],
  verified_harness_summary=re.findall(r'Complete - .*',log),
  errors=[s for s in log.splitlines() if 'Failed Checks:' in s or 'VERIFICATION:- FAILED' in s]+([f'Time limit expired (exit {r["exit_status"]}); not a proof result.'] if r['exit_status']==124 else []),
  stdout_sha256=sha(d/'stdout.log'),stderr_sha256=sha(d/'stderr.log'),receipt=str((d/'receipt.json').relative_to(here)),
  scope='Exact numeric helper extraction, diagnostic externals not admitted' if wide else 'Exact scanner source cut; library and contracted scan harness scopes are separate'))
out=dict(schema='r4-transport-focused-host-v1',attempts=rows,
 rss_note='GNU time peak RSS is the timed process tree report. On timeout, it can omit killed unreaped descendants; cgroup_memory_peak_bytes is also retained and is total charged memory, not an RSS measurement. No timeout is passing evidence.',
 harness_note='source_sha256 identifies unchanged shipped source. scanner-final.rs.txt freezes final harness definitions; initial words/finish and fixed-length membership roots are unchanged at their tested scopes. Historical full-crate hashes were not captured before adding unused harnesses; no full frozen replay claim is made.',
 optimized_note='Kani symbolic verification uses its own compiler pipeline. Native Charon crate preflight used --release; no dense arithmetic gate ran in a debug native binary.')
(here/'host-manifest.json').write_text(json.dumps(out,indent=2)+'\n')
print([(a['attempt'],a['exit']) for a in rows])
