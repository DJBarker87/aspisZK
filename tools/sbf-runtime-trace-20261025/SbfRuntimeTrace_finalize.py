"""Separate report/receipt serialization; no validation, host, or suite rerun."""
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

START=time.monotonic()
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=ROOT/'evidence/sbf-runtime-trace-20261025'
def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def load(name):return json.loads((OUT/name).read_text())
def save(name,value):(OUT/name).write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')
x=load('SbfRuntimeTrace-transport.stdout')
c=load('SbfRuntimeTrace-coverage.json')
t=load('SbfRuntimeTrace-transport-receipt.json')
a=load('SbfRuntimeTrace-analysis-receipt.json')
p=load('SbfRuntimeTrace-parsed.json')
n=load('SbfRuntimeTrace-native-inputs.json')
opened=load('SbfRuntimeTrace-opened-inputs.json')
final_mapped={r['path'] for r in n['mapped']}
final_unmapped=[dict(o,absent_from_final_maps=True) for o in opened if o['classification']=='pinned-regular' and o['physical_pin'] not in final_mapped]
save('SbfRuntimeTrace-final-map-coverage.json',dict(
    scope='derived report only; ever mapped and absent from final own maps differ',
    ever_unmapped_pinned_regular_paths=c['opened_unmapped_pinned_regular_paths'],
    absent_from_final_maps_pinned_regular_paths=sorted({o['path'] for o in final_unmapped}),
    absent_from_final_maps_open_records=final_unmapped,
    ld_cache='actual successful open and mmap/munmap in trace, fresh pin, absent from final maps',
    config='localtime fresh finite chain/pin; SSL config successful open but denied before endpoint pin',
    open_to_inode_binding='OPEN; own-map associations only establish mapped-file device/inode correspondence'))
g=x['guard']
report=f'''# SbfRuntimeTrace handoff

Branch codex/cx-sbf-runtime-trace-20261025; entry
338af425c97277de9bb3c9bd7d6f7c4841cc6f53. Only the assigned two directories
changed. No merge/push. Both deployed targets NOT ESTABLISHED. Runtime approval
and producer assembly NULL/DISABLED. No theorem, premise, trust, shipped source,
protocol, wire, feature, security-contract or ELF-build change.

## Established finite observation

One charged SSH sequence executed the preregistered 40,628-byte payload
e4b177dd8a35864da454b4a0bf981f58013541eaba812ca7121dae74e11090b5 at
b5198f82c717133b788b4a84da3771f99f52fa9a. The only executable launch site
ran one installed /usr/bin/strace with one /usr/bin/python3 -I -S -B -c
ordinary-import/metadata tracee; no backend definitions or FIXED_PROBE executed.
The fixed tracee completed exit0; the collector later failed exit78. Full raw
trace {c['trace_bytes']} bytes / {c['trace_lines']} lines retained, plus exact
stdout/stderr, controlled argv, source/dependency pins and unchanged rlimits.
There were no split records, dup calls, clone calls or unexpected tracee PIDs
in this actual trace. Such fixture coverage is synthetic/reused, not native.

Actual parser data: {c['open_calls']} successful open calls,
{c['unique_open_paths']} distinct opened paths, {c['negative_calls']} negative
calls (30 ENOENT, 1 EINVAL), one initial exec, four fcntl calls, descriptor
close lifecycle retained. Parser grammar replay complete for these bytes only;
not a claim of loader law, open-to-inode identity, or runtime completeness.

The actual PT_INTERP /lib64/ld-linux-x86-64.so.2 has a complete root-owned
component chain: /lib64 -> usr/lib64, then
/usr/lib64/ld-linux-x86-64.so.2 -> ../lib/x86_64-linux-gnu/ld-linux-x86-64.so.2,
ending at {c['loader']['physical']}. Its fresh pin is
{c['loader']['pin']['sha256']} / {c['loader']['pin']['size']} bytes.
All components and link identities are retained. Intermediate /usr/lib64 is
not treated as a final public root. No guessed loader alias or version claim.

Fresh disk pins: {c['pinned_files']} regular files / {c['pinned_unique_bytes']}
unique bytes, {c['unique_elf_files']} unique ELF files (14 parse operations,
because strace was freshly read again), {c['pyc_files']} pyc headers,
{c['module_records']} module metadata records. The trace includes successful
loader-cache, localtime, SSL config and pyc opens. Twenty-nine pyc paths plus
localtime were never mmap-backed in the trace; loader cache was temporarily
mapped, then absent from final maps. The supplemental final-map report retains
all {len({o['path'] for o in final_unmapped})} pinned regular paths absent from
the final maps. SSL config remains an explicit unpinned successful input.
All 60 final file-backed map records associate with fresh disk pins by Linux
device/inode. This narrower mapped-file observation does not bind earlier open
syscalls to inodes. No source/cache executed-body equality is inferred.

The partial SbfLinux-tiny-v1 candidate has {c['candidate_rows']} exact-schema
rows / {c['candidate_copy_bytes']} copied bytes, each <=16MiB and total <=64MiB.
Physical endpoints remain; actual observed loader/SONAME/interpreter aliases
are explicit byte clones with full chain provenance and each copy counted.
No symlinks or rootfs assembled. All tracee DT_NEEDED names have unique observed
physical pin candidates; this is name/pin data, not native effect closure.
The tracer is excluded from the candidate; its own dependencies are recorded
as tool metadata and not falsely demanded of the tracee rootfs.

## Terminal obstruction and retained failures

Exact new error: `{x['error']['message']}`. Actual successful open was
/usr/lib/ssl/openssl.cnf; its root-owned symlink target /etc/ssl/openssl.cnf was
recorded, but the exception was keyed to the starting /etc spelling. Thus the
already-public /usr spelling failed the finite grammar. The target's stat,
remaining chain and content pin were not acquired. This source-policy
counterexample is retained, not a host incompatibility conclusion. No source
repair, requery, retry or second SSH followed. The source/cache metadata pin
loop after successful-open acquisition was never reached.

All old failures remain unchanged at entry: terminal78 on /usr/lib64 prefix,
85-file old universe, 86-row unapproved candidate, old exact guard/payload/stat/
hashes, original Python3.9 sys.orig_argv receipt failure exit1 with unknown lost
metrics. Lead's independent 3.12 audit is reused only as its historical source
assessment, never as retroactive old success or new identity/admission. Old
205 assertions and old 85-file hash universe were not rerun.

## Validation and resources

New local source fixtures: 76 checks exit0, synthetic root identities and a
resolved temporary fixture directory; no ownership check weakened. Seven
immutable SbfSeal real lines reused as rejected adversarial examples, not a
passing native parser suite. Pre-host source review: 9 checks exit0, exact guard
bytes/AST prefix, protected globals, one Popen site, no resource setter, fixed
ordinary tracee imports. New local retained-data audit: 116 checks exit0,
wall {a['wall_seconds']}s, peak RSS {a['peak_rss_bytes']} bytes,
swap {a['swap_operations']}; compatible argv fallback/source recorded. Internal
metrics are sampled before receipt serialization; tool-reported process wall
is separately retained in the execution note. Finalizer is serialization only.

Transport exit78, wall {t['wall_seconds']}s; remote collector wall
{x['wall_seconds']}s; process peak {x['process_peak_rss_bytes']} bytes;
cumulative owned-child peak {x['child_peak_rss_bytes']} bytes; original guard
sampled aggregate peak {g['peak_sampled_rss_bytes']} bytes over
{len(g['samples'])} samples, exactly collector/tracer/tracee lineage. Both child
TGIDs were held until sampled together before import release. Guard error NULL;
failure cleanup found both children disappeared, no numeric PID signal.
Process swap operations {x['swap_operations']}; cgroup swap/pressure/peak and
aggregate reservations UNOBSERVED under the specific focused metadata exception.
No scope/build/reservation/GO claim. Sampling is not continuous; bootstrap
precedes monitor startup. All limits unchanged, no AS/DATA setters.

Budget used: SSH1/1, strace1/1, tracee exec1/1. All compiler/Lean/Cargo/Rust/Kani/
backend/extraction/ELFbuild/root/sudo/namespace/mount/credential/rlimit-change/
private guest/key/RPC budgets ZERO. Axioms N/A throughout (data, no theorem).
No assumptions discharged, added or weakened. No keys read/created/deleted.
No host stage files created. Finalizer and audit receipts are separate.

## Next concrete deliverable

Separately reviewed bounded acquisition source must recognize the exact
observed SSL-config alias in either starting spelling while still checking
every root-owned component and the final explicitly allowed config endpoint.
It needs a new source fixture for this retained counterexample and fresh
authority before any host call; the current epoch is exhausted. Candidate
eligibility remains false. Open-to-inode identity, cache executed-body binding,
conditional/dlopen/locale/NSS coverage, private PID1/resource/stdio/cancellation/
postexec, and fresh producer/control assembly remain open. SDK criterion
UNENTERED; no whole Cargo/ELF/native-memory or cryptographic-security claim.
'''
(OUT/'SbfRuntimeTrace-REPORT.md').write_text(report)
save('SbfRuntimeTrace-FAILURES.json',dict(
    historical=dict(revision='338af425c9',directory='evidence/sbf-runtime-20261025',
                    unchanged=True,old_remote_exit=78,old_local_audit_exit=1,old_local_lost_metrics='UNOBSERVED'),
    current=dict(source_revision=t['source_revision'],payload=t['payload'],exit=t['exit'],
                 exact_error=x['error'],failed_attempt=x['path_attempts'][-1],
                 retained_counterexample='public /usr/lib/ssl/openssl.cnf points to allowed /etc spelling, but config exception depends on original spelling',
                 retried=False,host_source_changed_after_failure=False),
    assumptions='unchanged; no theorem/premise changes',axioms='N/A'))
save('SbfRuntimeTrace-finalizer-receipt.json',dict(target='report/receipt serialization only, no validation',
    argv=getattr(sys,'orig_argv',sys.argv),argv_source='sys.orig_argv' if hasattr(sys,'orig_argv') else 'sys.argv',
    source_revision=t['source_revision'],exit=0,wall_seconds=time.monotonic()-START,
    peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024),swap_operations=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,
    aggregate_rss='UNOBSERVED; tiny local serialization',axioms='N/A',
    python=dict(executable=sys.executable,version=sys.version,binary_pin=pin(Path(sys.executable).read_bytes())),
    source=pin(Path(__file__).read_bytes()),
    dependencies={name:dict(file=getattr(m,'__file__',None),pin=pin(Path(m.__file__).read_bytes()) if getattr(m,'__file__',None) and Path(m.__file__).is_file() else None) for name,m in sorted(sys.modules.items()) if m is not None}))
save('SbfRuntimeTrace-artifact-index.json',dict(source_revision=t['source_revision'],
    files={str(f.relative_to(ROOT)):pin(f.read_bytes()) for folder in (HERE,OUT) for f in sorted(folder.iterdir()) if f.is_file() and f.name!='SbfRuntimeTrace-artifact-index.json'},
    runtime_approval=None,producer_assembly=None,axioms='N/A'))
print(json.dumps(dict(report='SbfRuntimeTrace-REPORT.md',exit=0,validation=False)))
