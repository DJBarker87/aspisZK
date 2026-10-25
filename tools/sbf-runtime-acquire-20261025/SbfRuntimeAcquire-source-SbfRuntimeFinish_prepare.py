"""Local immutable Git/data assembly only. NEVER executes generated payload."""
import ast
import hashlib
import json
from pathlib import Path
import subprocess
import resource
import sys
import time

START = time.monotonic()

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = ROOT / 'evidence/sbf-runtime-finish-20261025'
TRACE = '2ce034b264'
PRODUCER = '20a0f5bb38'
PINS = {}


def blob(rev, path):
    raw = subprocess.check_output(['git', 'show', rev + ':' + path], cwd=ROOT)
    PINS[rev + ':' + path] = dict(size=len(raw), sha256=hashlib.sha256(raw).hexdigest())
    return raw


def save(name, value):
    raw = (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()
    if len(raw) > 5_000_000:
        raise ValueError('derived JSON must be external hash/size only')
    (OUT / name).write_bytes(raw)


x = json.loads(blob(TRACE, 'evidence/sbf-runtime-trace-20261025/SbfRuntimeTrace-transport.stdout'))
p = json.loads(blob(TRACE, 'evidence/sbf-runtime-trace-20261025/SbfRuntimeTrace-parsed.json'))
c = json.loads(blob(TRACE, 'evidence/sbf-runtime-trace-20261025/SbfRuntimeTrace-PARTIAL-CANDIDATE-NOT-APPROVED.json'))
# Complete immutable new sources/reports assessed; all file bytes hashed, Python
# parsed as source, never imported. Dependency code is not trusted execution.
for rev, prefix in ((TRACE, 'tools/sbf-runtime-trace-20261025/'),
                    (PRODUCER, 'tools/sbf-producer-20261025/')):
    names = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', rev, prefix], cwd=ROOT).decode().splitlines()
    for path in names:
        raw = blob(rev, path)
        if path.endswith(('.py', '.py.txt')):
            ast.parse(raw)
for rev, path in ((TRACE, 'evidence/sbf-runtime-trace-20261025/SbfRuntimeTrace-REPORT.md'),
                  (TRACE, 'evidence/sbf-runtime-trace-20261025/SbfRuntimeTrace-FAILURES.json')):
    blob(rev, path)
rows = {}
opens = {r['path'] for r in p['opens']}
old_attempts = {a['path']: a for a in x['path_attempts'] if a['status'] == 'OBSERVED'}


def add(path, provenance, physical=None):
    if not path:
        return
    row = rows.setdefault(path, dict(path=path, provenance=[], observed_open=path in opens))
    row['provenance'].append(provenance)
    if physical in x['files']:
        row['old_pin'] = dict(physical=physical, **{k:x['files'][physical][k] for k in ('sha256','size','identity')})


for i, op in enumerate(p['opens']):
    a = old_attempts.get(op['path'], {})
    add(op['path'], dict(kind='REUSED_SUCCESSFUL_OPEN', record=i, event=op['index'], fd=op['fd'],
                         historical_inode_binding='OPEN'), a.get('physical'))
add('/usr/bin/python3', dict(kind='REUSED_ACTUAL_PYTHON_ENTRY'), x['python_entry'])
for physical, pin in x['files'].items():
    if physical == x['tracer_before']['physical']:
        continue
    if pin['elf']:
        for interp in pin['elf']['interpreter']:
            a = old_attempts.get(interp, {})
            add(interp, dict(kind='REUSED_PT_INTERP', owner=physical), a.get('physical'))
for row in c['files']:
    # Former candidate only establishes a possible alias if its actual old
    # chain reaches the pinned endpoint; never accept the candidate as authority.
    logical, physical = row['logical'], row['physical']
    if logical == physical and logical.startswith('/usr/share/zoneinfo/'):
        continue  # only reachable through exact /etc/localtime chain
    a = old_attempts.get(logical)
    if logical == physical or a and a['physical'] == physical:
        add(logical, dict(kind='REUSED_CHAIN_BACKED_ALIAS_OR_PHYSICAL', physical=physical), physical)
add('/etc/ssl/openssl.cnf', dict(kind='EXACT_FAILED_SSL_TARGET', observed_open=False,
                               negative_provenance='target stat/content/complete chain NOT acquired'))
module_fields = []
for name, module in sorted(x['tracee_metadata']['modules'].items()):
    for kind in ('file', 'cached'):
        path = module[kind]
        module_fields.append(dict(module=name, field=kind, path=path,
                                  classification='NO_PATH' if path is None else
                                  'REUSED_OPEN_PATH' if path in opens else 'PROSPECTIVE_FALLBACK'))
        add(path, dict(kind='EXACT_MODULE_FIELD', module=name, field=kind,
                       classification=module_fields[-1]['classification']), path)
for path, row in rows.items():
    a = old_attempts.get(path)
    if a:
        row['old_chain'] = a['components']
    elif path == x['path_attempts'][-1]['path']:
        row['old_chain'] = x['path_attempts'][-1]['components']
        row['old_chain_is_partial_negative_provenance'] = True
    row['classification'] = ('OWN_PROC_METADATA_NOT_REACQUIRED' if path == '/proc/self/maps' else
                              'DIRECTORY_METADATA' if a and a.get('components') and
                              a['components'][-1]['identity'][2] & 0o170000 == 0o040000 else 'FILE_CANDIDATE')
    row['old_pin_status'] = 'REUSED_LATER_DISK_PIN' if 'old_pin' in row else 'NO_HISTORICAL_PIN'
    if not row['observed_open']:
        row['historical_open_claim'] = False
plan = dict(candidate_template={k:v for k,v in c.items() if k != 'files'}, schema='SbfRuntimeFinish-finite-plan-v1', trace_revision=TRACE,
            paths=[rows[k] for k in sorted(rows)], modules=x['tracee_metadata']['modules'], module_fields=module_fields,
            old_trace=dict(lines=321, successful_opens=51, distinct_open_paths=49, pins=44, modules=68, pyc=29,
                           status='REUSED; NOT A NEW TRACE', open_fd_to_later_inode='OPEN'),
            failed_partial_chain=x['path_attempts'][-1], historical_negatives=p['negatives'],
            tool_dependencies=dict(tracer_excluded_from_guest=True, tracer=x['tracer_before'],
                                   dependencies='trace-tool metadata only; not inferred as guest requirements'),
            bounds=dict(file_bytes=16*2**20, unique_bytes=128*2**20, files=512, elf=64,
                        guest_copy_bytes=64*2**20, output_bytes=4*2**20, alarm_seconds=115,
                        prospective_ssh_seconds=120, rss_bytes=512*2**20),
            runtime_approval=None, producer_assembly=None)
save('SbfRuntimeFinish-plan.json', plan)
guard = blob('13abf7fe51', 'tools/resource-meta1g-20261025/ResourceMeta1G_guard.py')
assert hashlib.sha256(guard).hexdigest() == '9f0fbfd713895348a3df87fb4bb8643a85a4facb1d5ce95e31ad7839db74ca6d'
(HERE / 'SbfRuntimeFinish-guard.py.txt').write_bytes(guard)
elf = blob(TRACE, 'tools/sbf-runtime-trace-20261025/SbfRuntimeTrace-elf.py.txt')
(HERE / 'SbfRuntimeFinish-elf.py.txt').write_bytes(elf)
payload = guard + b'\n# END EXACT REVIEWED GUARD\n' + (HERE / 'SbfRuntimeFinish_core.py').read_bytes() + b'\n' + elf
payload += b'\nSBF_FINISH_PLAN = ' + repr(plan).encode() + b'\n' + (HERE / 'SbfRuntimeFinish_acquire.py.txt').read_bytes()
ast.parse(payload)
(HERE / 'SbfRuntimeFinish_payload.py.txt').write_bytes(payload)
save('SbfRuntimeFinish-immutable-inputs.json', dict(inputs=PINS, assessment='REUSED immutable Git only; not fresh identity/admission',
    unchanged_copies=['guard exact 13ab bytes/AST/global prefix', 'ELF parser exact 2ce bytes'],
    explicit_deltas=['new core replaces old walker; symmetric exact SSL pair; stricter config redirects, uid+gid, link nlink checks',
                     'hold all component FDs and recheck after hashing; no old walk/hash/path reopen',
                     'new acquisition loops fixed plan; no tracee/tracer/import execution; source/cache candidates not only positive trace paths'],
    payload=dict(size=len(payload), sha256=hashlib.sha256(payload).hexdigest()), executed=False))
usage = resource.getrusage(resource.RUSAGE_SELF)
def localpin(path):
    raw = path.read_bytes()
    return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
save('SbfRuntimeFinish-prepare-receipt.json', dict(
    target='immutable Git/data assembly; no payload/installer/transport execution',
    command=[sys.executable,*getattr(sys,'orig_argv',sys.argv)[1:]],
    source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),
    source_overlay={p.name:localpin(p) for p in HERE.iterdir() if p.is_file()},
    exit=0,wall_seconds=time.monotonic()-START,
    peak_rss_bytes=usage.ru_maxrss*(1 if sys.platform=='darwin' else 1024),swap=usage.ru_nswap,
    child_peak_rss_bytes=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss*(1 if sys.platform=='darwin' else 1024),
    dependencies={n:dict(path=m.__file__,**localpin(Path(m.__file__))) for n,m in sorted(sys.modules.items()) if getattr(m,'__file__',None) and Path(m.__file__).is_file()},
    interpreter=dict(path=sys.executable,version=sys.version,**localpin(Path(sys.executable))),
    print_axioms='N/A; no Lean/theorems',actual_host_budget_used=0,payload_executed=False,
    prior_assemblies='earlier preparation runs recorded by tool exit/wall only; peak RSS/swap UNOBSERVED; not validation gates'))
print(json.dumps(dict(paths=len(rows), module_fields=len(module_fields), payload_bytes=len(payload), executed=False)))
