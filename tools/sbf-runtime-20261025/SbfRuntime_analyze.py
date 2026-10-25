"""One local finite source/pin/schema audit of retained data; no runtime execution."""
import ast
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys
import time

START=time.monotonic()
ROOT=Path(__file__).parent.parent.parent
TOOLS=ROOT/'tools/sbf-runtime-20261025'
OUT=ROOT/'evidence/sbf-runtime-20261025'
def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def save(name,data):(OUT/name).write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
def gitblob(rev,path):return subprocess.check_output(['git','show',rev+':'+path],cwd=ROOT)
raw=(OUT/'SbfRuntime-transport.stdout').read_bytes()
x=json.loads(raw)
t=json.loads((OUT/'SbfRuntime-transport-receipt.json').read_text())
pr=json.loads((OUT/'SbfRuntime-preregister.json').read_text())
sources=json.loads((OUT/'SbfRuntime-source-inputs.json').read_text())
checks=[]
def check(name,condition):
    checks.append(dict(check=name,passed=bool(condition)))
    if not condition:raise ValueError(name)
check('raw transport output pin',pin(raw)==t['stdout'])
check('raw transport stderr pin',pin((OUT/'SbfRuntime-transport.stderr').read_bytes())==t['stderr'])
check('terminal remote failure preserved',t['exit']==78 and x['status']=='UNKNOWN' and x['error']==dict(type='GuardError',message='symlink target outside public roots: /usr/lib64'))
for label in ('abi','backend','capture','entry'):
    original=gitblob('9f50be799e','tools/sbf-linux-20261025/SbfLinux_'+label+'.py')
    check('immutable '+label+' byte identity',original==(TOOLS/f'SbfRuntime-{label}.py.txt').read_bytes())
guard=gitblob('13abf7fe51','tools/resource-meta1g-20261025/ResourceMeta1G_guard.py')
check('immutable guard byte identity',guard==(TOOLS/'SbfRuntime-guard.py.txt').read_bytes())
payload=(TOOLS/'SbfRuntime_payload.py.txt').read_bytes()
check('exact guard substring and payload pin',payload.count(guard)==1 and pin(payload)==pr['payload']==t['payload'])
# No compiler invocation: AST is syntax/data inspection; no project definitions run.
tree=ast.parse(payload)
functions={n.name:ast.dump(n,include_attributes=False) for n in tree.body if isinstance(n,(ast.FunctionDef,ast.ClassDef))}
for node in ast.parse(guard).body:
    if isinstance(node,(ast.FunctionDef,ast.ClassDef)):
        check('unchanged guard definition '+node.name,functions[node.name]==ast.dump(node,include_attributes=False))
for path,expected in pr['sources'].items():check('preregistered pin '+path,pin((ROOT/path).read_bytes())==expected)
check('interpreter fresh historical identity',x['fresh_interpreter_matches_historical_pin'] is True)
check('original guard successful',x['guard']['error'] is None and not x['guard']['cancellations'])
check('guard tracked only collector TGID',len(x['guard']['lineage'])==1 and all(len(s['processes'])==1 for s in x['guard']['samples']))
check('guard all samples below budget',all(s['rss_bytes']<=512*2**20 for s in x['guard']['samples']))
check('inherited rlimits unchanged',x['inherited_limits_before']==x['inherited_limits_after'])
check('bounded data',len(raw)<=4*2**20 and len(x['files'])<=512 and x['selected_unique_file_bytes']<=128*2**20 and x['elf_count']<=64)
check('time bounded',x['wall_seconds']<115 and t['wall_seconds']<120)
check('source/observer runtime approval absent',x['runtime_approval'] is None and x['producer_assembly'] is None)
rows=[]
# Exact observed regular files remain at their physical logical positions.
# The interpreter's /usr/bin/python3 entry is an explicit byte clone mapping,
# not a claim that the original symlink was captured or executed in a guest.
for physical,row in sorted(x['files'].items()):
    check('root stable bounded '+physical,row['uid']==0 and not row['mode']&0o022 and row['nlink']==1 and row['stable_open_fd_prepost'] and row['size']<=16*2**20)
    rows.append(dict(physical=physical,logical=physical,sha256=row['sha256'],size=row['size'],mode=0o555 if row['mode']&0o111 else 0o444))
interp=x['chains']['/usr/bin/python3']['physical']
entry=next(r for r in rows if r['physical']==interp)
rows.append(dict(entry,logical='/usr/bin/python3'))
candidate=dict(version='SbfLinux-tiny-v1',root=sources['root'],uid=1000,gid=1000,
               argv=sources['fixed_probe'],env=sources['env'],files=rows)
# Match the immutable schema statically, without executing imported backend code.
check('candidate exact schema',set(candidate)=={'version','root','uid','gid','argv','env','files'})
check('candidate finite capture bounds',0<len(rows)<=256 and sum(r['size'] for r in rows)<=64*2**20 and all(r['size']<=16*2**20 for r in rows))
check('candidate paths unique/reserved',len({r['logical'] for r in rows})==len(rows) and all(r['logical'].split('/')[1] not in ('tmp','proc','dev') for r in rows))
for row in rows:
    check('candidate pin/schema '+row['logical'],set(row)=={'physical','logical','sha256','size','mode'} and row['mode'] in (0o444,0o555) and len(row['sha256'])==64)
save('SbfRuntime-PARTIAL-CANDIDATE-NOT-APPROVED.json',candidate)
# Data-only ELF dynamic resolution against retained actual maps.
mapped=x.get('mapped_files',{})
lookup={}
for path in mapped:
    e=x['files'][path]['elf']
    for name in [Path(path).name]+(e['soname'] if e else []):lookup.setdefault(name,set()).add(path)
needed=[]
for path,row in sorted(x['files'].items()):
    if row['elf']:
        for name in row['elf']['needed']:
            observed=sorted(lookup.get(name,[]))
            guessed=[str(Path(p).parent/name) for p in observed]
            needed.append(dict(source=path,needed=name,mapped_candidates=observed,
                association='observed dev/inode map only; no loader search/effect law',
                logical_candidates_unvalidated=guessed,
                candidate_contains_name=any(Path(r['logical']).name==name for r in rows)))
pycs={p:r['pyc'] for p,r in x['files'].items() if 'pyc' in r}
pairs=[]
for name,m in sorted(x.get('modules',{}).items()):
    if m.get('cached'):
        source=x['files'].get(m.get('file_physical'))
        pyc=x['files'].get(m.get('cached_physical'))
        h=(pyc or {}).get('pyc',{})
        pairs.append(dict(module=name,source=m.get('file_physical'),cached=m['cached'],cached_present=bool(pyc),
            timestamp_and_size_match=(h.get('timestamp')==source['mtime_ns']//10**9 and h.get('source_size')==source['size']) if source and h.get('classification')=='timestamp-based' else None,
            executed_body_binding='OPEN; no unmarshalling/executing pyc or equivalence claim'))
historical=json.loads((OUT/'SbfRuntime-historical-runtime.json').read_text())
comparisons=[]
for path,row in x['files'].items():
    old=historical['mapped_libraries'].get(path)
    if old:comparisons.append(dict(path=path,fresh={k:row[k] for k in ('sha256','size')},historical=old,equal={k:row[k] for k in ('sha256','size')}==old))
summary=dict(status='PARTIAL DATA; candidate adoption STOPPED',eligible=False,complete=False,
    exact_error=x['error'],error_scope='acquisition prefix grammar rejected intermediate /usr/lib64; full loader chain was not exported; host incompatibility NOT established',
    file_count=len(x['files']),fresh_unique_bytes=x['selected_unique_file_bytes'],elf_count=x['elf_count'],
    loaded_module_count=len(x.get('modules',{})),audit_open_count=len(x['import_open_events']),pyc_count=len(pycs),
    candidate_rows=len(rows),candidate_bytes=sum(r['size'] for r in rows),
    explicit_clone=dict(physical=interp,logical='/usr/bin/python3',status='data-only explicit candidate mapping; not runtime-approved',chain=x['chains']['/usr/bin/python3']),
    physical_logical_policy='all other files preserve observed physical positions; no guessed stdlib/loader aliases added',
    elf_needed=needed,pyc_pairs=pairs,pyc_headers=pycs,
    historical_selected_mapped_comparisons=comparisons,
    missing_obligations=[
        'PT_INTERP /lib64/ld-linux-x86-64.so.2 chain encountered /usr/lib64; endpoint/ownership/link-chain completion UNOBSERVED; no retry permitted',
        'candidate has no approved /lib64 loader entry; dynamic SONAME lookup paths/aliases require explicit chain evidence',
        'audit hook is post-bootstrap and does not trace native loader/cache/opened-unmapped inputs',
        'all selected observer module files include incidental acquisition dependencies; no minimal FIXED_PROBE execution closure established',
        'sys.modules and maps are observations, not full conditional/dlopen/codec/locale/NSS coverage',
        'pyc header/hash/source pin observations do not prove which body executed or source-body equivalence',
        'private proc/PID1/mount/resource/stdio/cancellation/postexec coverage requires separately authorized actual probe',
        'fresh producer/sudo-monitor/helper ancestry and current resource gates remain missing; historical marker is metadata only'],
    runtime_approval=None,producer_assembly=None,SDK_external_criterion='UNENTERED',both_deployed_targets='NOT ESTABLISHED',
    budgets=dict(ssh_transport=1,metadata_sequence=1,compiler=0,lean=0,rust=0,cargo=0,kani=0,backend=0,elf_build=0,root=0,guest=0,rpc=0),
    reused='immutable source/guard bytes and historical selected runtime pins only; no identity/admission gate reused',
    new='one terminal finite observation plus this one local finite source/pin/schema audit; no runtime test',
    assumptions_changed='none; no theorem premise change or new trust assumption',axioms='N/A')
save('SbfRuntime-coverage.json',summary)
receipt=dict(target='retained finite SbfRuntime data/source/candidate schema',argv=sys.orig_argv,
    source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
    checks=checks,exit=0,wall_seconds=time.monotonic()-START,
    peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024),
    swap_operations=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,
    aggregate_rss='UNOBSERVED local tiny data audit; no build',axioms='N/A',
    inputs={p.name:pin(p.read_bytes()) for p in [OUT/'SbfRuntime-transport.stdout',OUT/'SbfRuntime-transport.stderr',OUT/'SbfRuntime-transport-receipt.json',OUT/'SbfRuntime-preregister.json',OUT/'SbfRuntime-source-inputs.json',Path(__file__)]},
    outputs={name:pin((OUT/name).read_bytes()) for name in ['SbfRuntime-coverage.json','SbfRuntime-PARTIAL-CANDIDATE-NOT-APPROVED.json']},
    python=dict(executable=sys.executable,version=sys.version),
    dependency_pins={name:dict(file=getattr(m,'__file__',None),cached=getattr(m,'__cached__',None),pin=pin(Path(m.__file__).read_bytes()) if getattr(m,'__file__',None) and Path(m.__file__).is_file() else None) for name,m in sorted(sys.modules.items()) if m is not None})
save('SbfRuntime-local-audit-receipt.json',receipt)
print(json.dumps({k:summary[k] for k in ('status','eligible','file_count','fresh_unique_bytes','elf_count','loaded_module_count','audit_open_count','pyc_count','candidate_rows','candidate_bytes')},sort_keys=True))
print('finite checks:',len(checks),'exit: 0')
