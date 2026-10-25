"""Receipt/report serialization only; no repeat validation or host access."""
import hashlib
import json
from pathlib import Path
import resource
import sys
import time
START=time.monotonic()
ROOT=Path(__file__).parent.parent.parent
OUT=ROOT/'evidence/sbf-runtime-20261025'
TOOLS=ROOT/'tools/sbf-runtime-20261025'
def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def save(name,data):(OUT/name).write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
x=json.loads((OUT/'SbfRuntime-transport.stdout').read_bytes())
c=json.loads((OUT/'SbfRuntime-coverage.json').read_text())
t=json.loads((OUT/'SbfRuntime-transport-receipt.json').read_text())
save('SbfRuntime-local-audit-receipt.json',dict(
    status='FAILED RECEIPT SERIALIZATION; not an exit-zero audit',
    argv=['/usr/bin/python3','-I','-S','-B','tools/sbf-runtime-20261025/SbfRuntime_analyze.py'],
    source_revision=t['source_revision'],exit=1,wall_seconds=0.099915875,
    wall_source='exec tool-reported process duration; no internal successful receipt',
    peak_rss_bytes='UNOBSERVED',swap_operations='UNOBSERVED',aggregate_rss='UNOBSERVED',
    local_python_dependency_execution_binding='UNOBSERVED; failure prevented dependency receipt',
    error='AttributeError: module sys has no attribute orig_argv',
    reached='line126 receipt constructor after all preceding checks and two output writes; no rerun',
    source=pin((TOOLS/'SbfRuntime_analyze.py').read_bytes()),
    raw_error=pin((OUT/'SbfRuntime-local-audit-failure.log').read_bytes()),
    inputs={name:pin((OUT/name).read_bytes()) for name in ['SbfRuntime-transport.stdout','SbfRuntime-transport.stderr','SbfRuntime-transport-receipt.json','SbfRuntime-preregister.json','SbfRuntime-source-inputs.json']},
    outputs={name:pin((OUT/name).read_bytes()) for name in ['SbfRuntime-coverage.json','SbfRuntime-PARTIAL-CANDIDATE-NOT-APPROVED.json']},
    axes='N/A; raw data/source/schema audit, no theorem'))
missing_names=sorted({r['needed'] for r in c['elf_needed'] if not r['candidate_contains_name']})
report=f'''# SbfRuntime handoff

Branch codex/cx-sbf-runtime-20261025; entry ae091370b6c3f7bd2cba1fdc511197ff0cc90998.
All changes are confined to tools/sbf-runtime-20261025 and evidence/sbf-runtime-20261025.

Established new data: one SSH transport, exit {t['exit']}, transport wall
{t['wall_seconds']}s. Remote finite payload wall {x['wall_seconds']}s;
{c['file_count']} freshly hashed regular files, {c['fresh_unique_bytes']} bytes,
{c['elf_count']} ELF metadata records, {c['loaded_module_count']} loaded module records,
{c['audit_open_count']} post-hook import open events, {c['pyc_count']} pyc files.
Fresh CPython pin equals the historical pinned interpreter; selected historical
mapped-file comparisons are retained individually in coverage.json. This is
new finite metadata, not a new artifact identity/admission/runtime gate.

Process ru_maxrss {x['process_peak_rss_bytes']} bytes, ru_nswap
{x['process_swap_operations']}; exact guard sampled aggregate peak
{x['guard']['peak_sampled_rss_bytes']} bytes, {len(x['guard']['samples'])} samples,
one tracked TGID, no descendants, no guard error/cancellations. Full samples,
lineage, initial/final unchanged rlimits and exact commands/source/dependency
pins are retained. Sampled RSS is not continuous; cgroup pressure/peak/swap and
aggregate populated reservations were UNOBSERVED under the specific metadata
exception. No scoped/build/consumer/GO permission is claimed. Startup precedes
the resident sampling; process ru_maxrss includes its high-water observation.

The payload returned UNKNOWN/78 on exactly:
`symlink target outside public roots: /usr/lib64`.
PT_INTERP is /lib64/ld-linux-x86-64.so.2. The remaining chain was not exported;
this failure concerns the acquisition's immediate-prefix grammar and cannot
establish host runtime incompatibility. No retry, query, repair or further SSH.

The partial SbfLinux-tiny-v1 schema candidate has {c['candidate_rows']} rows,
{c['candidate_bytes']} copied bytes, 16MiB/file and 64MiB total bounds respected.
It retains physical positions and explicitly maps the pinned binary also to
/usr/bin/python3. It has no approved loader entry or guessed aliases. Missing
DT_NEEDED lookup names in these rows: {', '.join(missing_names) or 'none by basename; this would still not prove lookup closure'}.
Adoption STOPPED, eligible=false, completeness=false. Module/maps observations
include incidental observer dependencies and a mapped gconv cache; native
unmapped inputs, conditional imports, locales/NSS/codecs, bootstrap and pyc
executed-body binding remain OPEN. No blanket source-only import assumption.

One local finite source/pin/schema audit checked immutable source/guard bytes,
retained pins, guard/limit/bounds and candidate structure. It reached receipt
serialization and failed on unavailable local sys.orig_argv, exit1, tool wall
0.099915875s. All preceding checks and two output writes completed; this is
not a clean exit-zero result. Its lost peak/swap/dependency metrics are marked
UNOBSERVED. Error/source retained; no unchanged regression/check rerun. Final
serialization only recovers receipts/reports and does not revalidate.

Reused: immutable 9f50be799e source and 13abf7fe51 exact guard plus historical
c7bbb274e2 selected runtime pins only. No producer/approval/CLI/source contract
changed; no assumptions discharged, added or weakened. Axioms N/A throughout.
SSH/metadata budget used 1/1. Compiler, Lean, Cargo, Rust, Kani, backend,
ELF/native proof, root/sudo/ns/mount/credential/rlimit-change/guest/RPC/key
budgets used ZERO. Kani59/60 reserved, all six old resource failures charged.
No merge/push; no keys or host stage files created/deleted.

Next deliverable: a newly allocated reviewed finite acquisition that handles
and exports the complete permitted loader alias chain, plus native loader/
opened-unmapped import coverage. Fresh producer ancestry/control assembly and
separately authorized finite cancellation/private-proc/resource/stdio/postexec
probe remain necessary. SDK external criterion UNENTERED. Both deployed
targets NOT ESTABLISHED. See REQUIREMENTS.md and FAILURES.md for exact retained
boundaries and failure interpretation; raw stdout is immutable evidence.
'''
(OUT/'SbfRuntime-REPORT.md').write_text(report)
receipt=dict(target='receipt/report serialization only; no tests/revalidation',
    argv=[sys.executable,'-I','-S','-B','tools/sbf-runtime-20261025/SbfRuntime_finalize.py'],
    source_revision=t['source_revision'],python=dict(executable=sys.executable,version=sys.version,
        binary=pin(Path(sys.executable).read_bytes())),
    source=pin(Path(__file__).read_bytes()),exit=0,wall_seconds=time.monotonic()-START,
    peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024),
    swap_operations=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,
    aggregate_rss='UNOBSERVED; tiny local serialization, no children',axioms='N/A',
    dependencies={n:dict(file=getattr(m,'__file__',None),source_pin=pin(Path(m.__file__).read_bytes()) if getattr(m,'__file__',None) and Path(m.__file__).is_file() else None,body_binding='not established by associated source hash') for n,m in sorted(sys.modules.items()) if m is not None})
save('SbfRuntime-finalization-receipt.json',receipt)
save('SbfRuntime-artifact-index.json',dict(source_revision=t['source_revision'],
    files={str(p.relative_to(ROOT)):pin(p.read_bytes()) for folder in (TOOLS,OUT) for p in sorted(folder.iterdir()) if p.is_file() and p.name!='SbfRuntime-artifact-index.json'},
    axioms='N/A',approval=False))
print(json.dumps({k:c[k] for k in ('status','file_count','fresh_unique_bytes','elf_count','loaded_module_count','audit_open_count','pyc_count','candidate_rows','candidate_bytes')},sort_keys=True))
print('missing DT_NEEDED basenames:',', '.join(missing_names))
