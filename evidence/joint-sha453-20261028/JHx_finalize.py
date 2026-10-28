"""Final exact-source evidence audit and handoff; does not launch Lean."""
from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];L=R/'lean'
subprocess.run(['python3',str(E/'JHx_generate.py'),'--check'],check=True)
subprocess.run(['python3',str(E/'JHx_source_audit.py')],check=True)
subprocess.run(['python3',str(E/'JHx_validate.py')],check=True)
v=json.loads((E/'JHx_VALIDATION.json').read_text());assert v['passed']
compare=json.loads((E/'JHx_STATEMENT_COMPARE.json').read_text());assert compare['equal_after_removing_only_sha_binder']
rows=[json.loads(x) for x in (E/'JHx_ATTEMPTS.jsonl').read_text().splitlines()];current=v['results']
assert all(str(r['swaps'])=='0' for r in rows)
for r in rows:
 a=json.loads((E/(r['attempt']+'-admission.json')).read_text())[-1]
 assert a['exit_status']==0 and a['receipt']['allowed'] is True
 limit=r['limits'];assert limit['memory.swap.max']=='0' and limit['pids.max']=='64'
 assert limit['memory.max']==str((16 if r['mode']=='large' else 8)*1024**3)
files={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.glob('JHx_*.lean'))}
(E/'JHx_FINAL_SOURCES.json').write_text(json.dumps(files,indent=2)+'\n')
byname={r['module']:r for r in current};inst=byname['JHx_Instance'];joint=byname['JHx_Joint']
text=f'''# SHA453 realization and joint witness handoff

The requested local fixture obligation is established. `AspisR1.JHx_Instance.source`
proves `JHe_SHARealization` unconditionally, and `JHx_Instance.realization` installs
it. `AspisR1.JHx_Joint.source` supplies that instance to `JHw_Joint.source`.
All delivered theorems use only propext, Classical.choice, Quot.sound or subsets.
No native_decide or added axioms. No push or merge.

## Before and after

Before: `JHw_Joint.source [trees : JHe_SHARealization] (base : AdapterRw.Ops)
(stage : VTop_Stages.Ops) (slot : U64) (runtime : FixturePdaRuntime base) : ...`.

After: `JHx_Joint.source (base : AdapterRw.Ops) (stage : VTop_Stages.Ops)
(slot : U64) (runtime : FixturePdaRuntime base) : ...`.

The entire existential conclusion is identical: one saved vector, original-world
TX1, corrected-world TX1, exact retained checkpoint bytes and length 1768, and TX2
acceptance on the same installed SDK. The two heaps remain explicit. Complete
statements: JHx_BEFORE.lean.txt and JHx_AFTER.lean.txt. The mechanical comparison
in JHx_STATEMENT_COMPARE.json confirms removal of only the named SHA binder;
no quantifier, dictionary, carrier, execution result or conclusion changed.
`FixturePdaRuntime base` is the sole remaining propositional hypothesis. Its
contents remain assumed; no native syscall/ELF fidelity or headline 100-bit
security claim follows from this local fixture result.

## Certificate method and checker

453 equations: tree0 Fin157, tree1 Fin157, tree2 Fin139;996 compression blocks.
JHx_generate.py independently checks each retained block's input/start/result,
all 64 SHA rounds, chaining, padding, source head/chunk definitions, input and
expected aliases, and all 453 complete digests with hashlib. `--check` validates
the exact generated source manifest. JHx_GENERATOR_CHECK.json records per-equation
digests, source pins and module hashes. Python is a preflight only; Lean checks
every concrete round. Pure arithmetic modules import JFp_SHA256 only. Equation
modules apply their compiled certificates and symbolic list/padding/hash joins.
Every delivered helper theorem has a #print axioms audit. JHx_SOURCE_AUDIT.json
records the broad-unfolding scan. JHx_FINAL_SOURCES.json pins delivered sources.

## Validation and resources

{len(current)} canonical modules have passing exact-source receipts. Budget usage:
{v['normal_attempts']}/60 normal attempts;{v['agg16_attempts']}/2 approved16GiB attempts.
Every attempt (including failures) is in JHx_ATTEMPTS.jsonl and its numbered
receipt directory: target/argv, source revision and hash, direct object and tool
pins, exit, wall, peakRSS, swap, cgroup limits and full axioms output. Admission
requires exit0 AND allowed:true. One scope at a time. All swap counts0.

Instance: {inst['attempt']}, exit0, wall{inst['wall_seconds']:.6f}s,
peakRSS{inst['peak_rss_kib']}KiB, swap0, source revision{inst['source_revision']}.
Joint: {joint['attempt']}, exit0, wall{joint['wall_seconds']:.6f}s,
peakRSS{joint['peak_rss_kib']}KiB, swap0, source revision{joint['source_revision']}.
Their complete standard-axiom audits are in JHx_VALIDATION.json and stdout logs.
Total Lean wall{sum(r['wall_seconds'] for r in rows):.6f}s;
maximum attemptRSS{max(int(r['peak_rss_kib']) for r in rows)}KiB.

001 failed memory after encountering padding/length/member proof errors;003
isolated the remaining padding recursion error. Rejected sorryAx diagnostics
receive no credit. Both were replaced by changed proof shapes; no unchanged
failed chunk was rerun. JHx_MEMORY_SPLIT001.md records the failures, focused
replacement and measured16→28→56-block scale. No arithmetic cap increase.
The successful probe is retained in004's source snapshot, outside the canonical
module list. No unchanged full regression or package build was run. Final
assembly and exact-source/axiom audits consume all checked chunks. Inherited
compiled dependencies were reused, not claimed as a fresh frozen release replay.

## Cache and preservation

Own retained cache: /home/dombarker/project-offloads/codex-cx-sha453-cache-20261028.
Seeded by copying .olean companions from the read-only tx2fix and fixture caches.
JHx_SEED_COLLISIONS.json confirms no differing overlapping seed objects. Original
cache directories were never changed. Normal caps6G/8G,swap0,TasksMax64,-M7000.
The approved agg16 runner hashes were verified against JHw_RUNNER_HASHES.json;
any actual agg16 use is separately receipted with14G/16G,-M15000. Source and
receipts only are committed; no binaries, objects or oversized logs. Work is
confined to new JHx modules and evidence/joint-sha453-20261028. Existing proved
modules, Rust, protocol, wallet keys and frozen artifacts are unchanged.

No remaining blocker for this requested SHA instance and local joint witness.
The broader security target is not established by these fixture proofs.
'''
(E/'JHx_HANDOFF.md').write_text(text)
print('Final handoff written')
