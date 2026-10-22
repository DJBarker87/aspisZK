#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent.parent
host='dombarker@100.108.41.90:';H='/home/dombarker/project-offloads/codex-cx-prover-commit14-20261021'
for f in ['word-split-results.json','kani-artifacts.json','rust-tools.json']:
 subprocess.run(['scp',host+H+'/'+f,str(E/f)],check=True)
results=json.loads((E/'word-split-results.json').read_text())
assert sorted(r['word'] for r in results)==list(range(8)) and all(r['exit_status']==0 for r in results)
rows=json.loads((E/'rust-attempts.json').read_text())
cases=sorted([r for r in rows if r['name'].startswith('m31-word')],key=lambda r:int(r['name'].split('word')[1].split('-')[0]))
assert len(cases)==9 and all(r['accepted'] for r in cases)
assert {r['word'] for r in json.loads((E/'kani-artifacts.json').read_text())}==set(range(9))
p=Path('docs/research/v8-r0-zk-20261009/r1p-final/PROVER-COMMIT14-20261021.md')
s=p.read_text().replace('The actual release target is not yet established. This report is updated by stage.',
'''The owned material recursions, retained-global-oracle support/window bridge,
and all nine bounded M31 cell gates pass. Complete shipped execution/history
and all-family coverage remain open. No headline premise is removed.
**The actual release target is not yet established.**''')
s+='''
## Completed word split and final handoff

All nine `state_only_hiding::material14::word_0` through `word_8` gates pass.
The earlier first-acceptance and legal-word partition theorems audited in
part 13 make these input cases exhaustive within the stated cell domain.
The exact status, command, source hashes, base revision, cgroup reservations,
limits, timing, RSS and swap are retained in `rust-attempts.json`, individual
receipts and input manifests. Kani `#print axioms` is N/A; its external
verifier/library trust boundary is separate from the Lean axiom audit.

| Initial word | Exit | Wall s | Peak RSS KiB | Cgroup peak bytes | Swap |
|---|---:|---:|---:|---:|---:|
'''
for r in cases:
 word=int(r['name'].split('word')[1].split('-')[0]);s+=f"| {word} | {r['exit_status']} | {r['wall_seconds']} | {r['peak_rss_kib']} | {r['cgroup_memory_peak_bytes']} | {r['swaps']} |\n"
s+='''
This certifies the lifted M31 cell for any legal initial word, first accepted
candidate or exhaustion, arbitrary retained scalar state, and an owned
vector prefix of length at most two. Kani retains its explicit no-malloc-
failure model. The source scalar is executed using its accepted verified
next-word callee, not an unproved scalar stub. Exact host proof-input binary
hashes/sizes are retained in `kani-artifacts.json`; no binary is committed.

The raw returned-value/state equality is not promoted to a proof of complete
adaptive callback history. The whole extracted owned recursions and their
generic one-step equations are proved in Lean, but arbitrary source vector
prefix transport, QM31 source-cell P6, all outer-column/returned-material
assembly, and actual builder/checker/retry execution still need their joins.
The actual source loop's prior preflighted Aeneas context-join failure is
not rerun unchanged or treated as an accepted extraction.

The source-history item stops at the checked observer handoff boundary:
unrestricted replacement programs do not preserve complete histories.
The callback-family item stops at the actual runtime/history instance;
reference support and nine-block local scalar oracles cannot supply that
instance or the full 4096-limb source run. No whole-run predicate, bad event,
query budget, carrier, adversary quantifier, numerical error term, security
target, or headline premise is weakened. `G_sim_R_wire` stays named.

The next concrete deliverable is a verified scalar summary in the
first-acceptance formulation, then universal source-prefix/QM31 and column
context transport to the owned reference, followed by the actual observer
program and builder/checker/retry history join. All-family shared-oracle
coverage must instantiate every seed, packing, D, salt, tree, retry and
abort callback in that same retained global execution. The old local-ROM
capacity counterexample remains valid; local resets do not close the join.

Final `harness/validate.py --check` is an evidence validation, not another
Lean build or unchanged regression. All scoped jobs are finished, proof
sources and receipts are committed, host caches and keys are retained.
No production Rust/Cargo/frozen ELF input or peer-owned file is changed.
There is no push or merge. Env J next available attempt remains **8390**.
'''
p.write_text(s)
m=json.loads((E/'manifest.json').read_text())
for f in (E/'rust-sources').glob('*'):m['sources'][str(f)]=hashlib.sha256(f.read_bytes()).hexdigest()
m['accepted_m31_word_cases']=list(range(9));m['source_cell_prefix_bound']=2
(E/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
print('Final report and manifest prepared; source/security scope remains explicit.')
