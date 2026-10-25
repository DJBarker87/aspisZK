"""One focused retained-data audit and partial candidate, no host execution."""
import hashlib
import json
from pathlib import Path
import resource
import runpy
import sys
import time

START=time.monotonic()
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=ROOT/'evidence/sbf-runtime-trace-20261025'
def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def save(name,value):(OUT/name).write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')
checks=[]
def check(name,ok):
    checks.append(dict(name=name,passed=bool(ok)))
    if not ok:raise ValueError(name)
error=None
try:
    raw=(OUT/'SbfRuntimeTrace-transport.stdout').read_bytes()
    x=json.loads(raw)
    t=json.loads((OUT/'SbfRuntimeTrace-transport-receipt.json').read_text())
    pr=json.loads((OUT/'SbfRuntimeTrace-preregister.json').read_text())
    inputs=json.loads((OUT/'SbfRuntimeTrace-sourcepins.json').read_text())
    check('transport complete bytes',pin(raw)==t['stdout'] and t['stdin_bytes_sent']==pr['payload']['size'] and t['terminal_error'] is None)
    check('terminal grammar failure preserved',t['exit']==78 and x['status']=='UNKNOWN' and x['error']==dict(type='ValueError',errno=None,message='symlink outside explicit paths: /etc/ssl/openssl.cnf'))
    for path,p in pr['sources'].items():check('preregistered source '+path,pin((ROOT/path).read_bytes())==p)
    for kind,content in x['raw'].items():
        b=content.encode('ascii');check('full raw pin '+kind,pin(b)==x['raw_pins'][kind])
        (OUT/('SbfRuntimeTrace-actual.'+kind)).write_bytes(b)
    check('output/time bounds',len(raw)<=4*2**20 and x['raw_pins']['trace']['size']<=16*2**20 and x['wall_seconds']<115 and t['wall_seconds']<120)
    check('fixed tracee completed once',x['trace_exit']==0 and x['handshake_released'] and x['tracee_metadata']['pid']==x['tracee_pid'] and x['tracee_metadata']['threads']==1)
    check('exact pre/post tracer identity',x['tracer_before']['sha256']==x['tracer_after']['sha256'] and x['tracer_before']['size']==x['tracer_after']['size'] and x['tracer_before']['chain']==x['tracer_after']['chain'])
    g=x['guard'];lineage={r['pid'] for r in g['lineage']}
    check('exact three owned TGIDs',len(lineage)==3 and {x['tracer_pid'],x['tracee_pid']}<lineage)
    check('guard observed tracer and tracee together',any(set(s['processes'])==lineage for s in g['samples']))
    check('guard sampled budget and no error',g['error'] is None and all(s['rss_bytes']<=512*2**20 for s in g['samples']))
    check('terminal cleanup no numeric signal',all(c['outcome']=='disappeared' for c in g['cancellations']))
    check('inherited limits identical',x['inherited_limits_before']==x['inherited_limits_after'])
    parse=runpy.run_path(str(HERE/'SbfRuntimeTrace_parse.py'))['parse']
    p=parse(x['raw']['trace'],x['tracee_pid'])
    check('local replay same host parser summary',{k:v for k,v in p.items() if k!='events'}==x['parser_summary'])
    check('actual captured grammar complete',p['complete'] and not p['errors'] and p['exec_count']==1 and p['pids']==[x['tracee_pid']])
    save('SbfRuntimeTrace-parsed.json',p)
    attempts=x['path_attempts'];files=x['files']
    bypath={}
    for a in attempts:
        if a['status']=='OBSERVED':
            if a['path'] in bypath:check('stable repeated path '+a['path'],bypath[a['path']]['physical']==a['physical'])
            bypath[a['path']]=a
    loader=files[x['python_entry']]['elf']['interpreter']
    check('actual PT_INTERP complete',loader==['/lib64/ld-linux-x86-64.so.2'] and loader[0] in bypath)
    check('loader endpoint pinned',bypath[loader[0]]['physical'] in files)
    check('failed config partial chain explicit',attempts[-1]['path']=='/usr/lib/ssl/openssl.cnf' and attempts[-1]['failed_component']=='/usr/lib/ssl/openssl.cnf' and attempts[-1]['symlinks'][-1]['target']=='/etc/ssl/openssl.cnf' and attempts[-1]['error_type']=='ValueError')
    check('new unique bytes accurate',sum(r['size'] for r in files.values())==x['unique_hashed_bytes'])
    check('all retained files bounded root stable',all(r['identity'][3]==0 and not r['identity'][2]&0o022 and r['identity'][5]==1 and r['size']<=16*2**20 and r['stable_fd'] for r in files.values()))
    check('no runtime/producer approval',x['runtime_approval'] is None and x['producer_assembly'] is None)
    # Only opened paths, exact interpreter and loader names; never guessed aliases.
    logical={o['path'] for o in p['opens']}|{'/usr/bin/python3'}|set(loader)
    selected={bypath[s]['physical'] for s in logical if s in bypath and bypath[s]['physical'] in files}
    rows={};reasons={}
    def mapping(logical,physical,reason):
        f=files[physical]
        row=dict(logical=logical,physical=physical,size=f['size'],sha256=f['sha256'],mode=0o555 if f['identity'][2]&0o111 else 0o444)
        if logical in rows:check('unique mapping identity '+logical,rows[logical]==row)
        rows[logical]=row;reasons.setdefault(logical,[]).append(reason)
    for physical in sorted(selected):mapping(physical,physical,'observed canonical physical endpoint preserved')
    for name in sorted(logical):
        if name in bypath and bypath[name]['physical'] in selected:
            mapping(name,bypath[name]['physical'],'explicit byte clone at observed lookup/entry name; full chain retained; no symlink created')
    candidate=dict(version='SbfLinux-tiny-v1',root=inputs['root'],uid=1000,gid=1000,argv=inputs['fixed_probe'],env=inputs['env'],files=sorted(rows.values(),key=lambda r:r['logical']))
    check('candidate immutable schema shape',set(candidate)=={'version','root','uid','gid','argv','env','files'} and all(set(r)=={'physical','logical','sha256','size','mode'} for r in rows.values()))
    check('candidate copy bounds',0<len(rows)<=256 and sum(r['size'] for r in rows.values())<=64*2**20 and all(r['size']<=16*2**20 for r in rows.values()))
    check('candidate paths distinct and unreserved',len(rows)==len(candidate['files']) and all(r['logical'].split('/')[1] not in ('tmp','proc','dev') for r in rows.values()))
    save('SbfRuntimeTrace-PARTIAL-CANDIDATE-NOT-APPROVED.json',candidate)
    save('SbfRuntimeTrace-mapping-reasons.json',reasons)
    opened=[]
    mapped_paths={m['path'] for m in p['mapped']}
    for o in p['opens']:
        a=bypath.get(o['path'],{});physical=a.get('physical');f=files.get(physical)
        opened.append(dict(o,physical_pin=physical if f else None,pin=dict(size=f['size'],sha256=f['sha256']) if f else None,
            ever_mapped=o['path'] in mapped_paths,
            classification='pinned-regular' if f else 'controlled-own-metadata' if o['path']=='/proc/self/maps' else 'observed-directory' if a and a['components'][-1]['identity'][2]&0o170000==0o040000 else 'OPEN-unpinned',
            open_to_physical_identity='OPEN; stable disk pin and trace labels are insufficient'))
    needed=[]
    for path in sorted(selected):
        e=files[path]['elf']
        if e:
            for name in e['needed']:
                matches=[r for r in rows.values() if Path(r['logical']).name==name and files[r['physical']]['elf']]
                needed.append(dict(source=path,name=name,actual_observed_logical_names=[r['logical'] for r in matches],physical_candidates=sorted({r['physical'] for r in matches}),status='observed-unique-pin' if len({r['physical'] for r in matches})==1 else 'OPEN',effect_law='OPEN'))
    mapped=[]
    for line in x['tracee_metadata']['maps'].splitlines():
        parts=line.split(None,5)
        if len(parts)!=6 or not parts[5].startswith('/'):continue
        address,perms,offset,dev,ino,path=parts;f=files.get(path)
        major,minor=(int(i,16) for i in dev.split(':'))
        # Linux dev_t encoding, independent of the local macOS os.major layout.
        device=f['identity'][0] if f else None
        observed_major=((device>>8)&0xfff)|((device>>32)&0xfffff000) if f else None
        observed_minor=(device&0xff)|((device>>12)&0xffffff00) if f else None
        mapped.append(dict(path=path,offset=int(offset,16),dev=dev,ino=int(ino),permissions=perms,
            pin_association=bool(f and (observed_major,observed_minor)==(major,minor) and f['identity'][1]==int(ino)),
            scope='actual mapped file only; not open syscall identity or native semantics'))
    save('SbfRuntimeTrace-opened-inputs.json',opened)
    save('SbfRuntimeTrace-native-inputs.json',dict(needed=needed,mapped=mapped,elfs={p:f['elf'] for p,f in files.items() if f['elf']},tracer_not_in_candidate=x['tracer_before']['physical'] not in selected))
    unmapped_regular=[o for o in opened if not o['ever_mapped'] and o['classification']=='pinned-regular']
    summary=dict(status='TERMINAL_PARTIAL; no retry',complete=False,eligible=False,
        parser_grammar_complete=p['complete'],parser_grammar_scope='one fixed host trace; not physical identity, closure or native effect law',
        exact_error=x['error'],trace_lines=len(p['events']),trace_bytes=x['raw_pins']['trace']['size'],exec_count=p['exec_count'],
        open_calls=len(opened),unique_open_paths=len({o['path'] for o in opened}),negative_calls=len(p['negatives']),
        negative_errno_counts={k:sum(n['errno']==k for n in p['negatives']) for k in sorted({n['errno'] for n in p['negatives']})},
        pinned_files=len(files),pinned_unique_bytes=sum(f['size'] for f in files.values()),unique_elf_files=sum(bool(f['elf']) for f in files.values()),elf_parse_operations=x['elf_count'],
        pyc_files=sum('pyc' in f for f in files.values()),module_records=len(x['tracee_metadata']['modules']),
        opened_unmapped_paths=len(p['opened_unmapped']),opened_unmapped_pinned_regular_calls=len(unmapped_regular),opened_unmapped_pinned_regular_paths=sorted({o['path'] for o in unmapped_regular}),
        opened_unpinned=[o['path'] for o in opened if o['classification']=='OPEN-unpinned'],
        candidate_rows=len(rows),candidate_copy_bytes=sum(r['size'] for r in rows.values()),
        loader=dict(logical=loader[0],physical=bypath[loader[0]]['physical'],full_chain=bypath[loader[0]],pin={k:files[bypath[loader[0]]['physical']][k] for k in ('sha256','size')}),
        missing_needed=[n for n in needed if n['status']=='OPEN'],all_mapped_file_pins_associated=all(m['pin_association'] for m in mapped),
        historical_interpreter_pin_equal={k:files[x['python_entry']][k] for k in ('sha256','size')}==inputs['historical_runtime']['executable_pin'],
        runtime_approval=None,producer_assembly=None,both_deployed_targets='NOT ESTABLISHED',axioms='N/A',
        source_assessment='all loader/trace-selected pins fresh; old source ASTs and guard reused immutably; no prior gate/admission reuse',
        assumptions_changed='none; no theorem or premise change',
        budgets=dict(ssh=1,controlled_strace=1,actual_tracee_exec=1,compiler=0,lean=0,cargo=0,rust=0,kani=0,backend=0,elf_build=0,root=0,sudo=0,namespace=0,mount=0,credential=0,rlimit_change=0,private_probe=0,key=0,rpc=0),
        gaps=['actual opened SSL config endpoint ownership and content pin unobserved after exact grammar denial',
              'source/cache body binding OPEN; source pin loop not reached; -B does not prevent cache reads',
              'trace labels do not establish successful-open inode identity; mapped-file associations have narrower scope',
              'fixed trace has no native completeness theorem; future conditional/dlopen/locale/NSS coverage OPEN',
              'private PID1/resources/stdio/cancellation/postexec and producer ancestry/control assembly remain OPEN',
              'cgroup pressure/swap/reservations unobserved; no GO or native cryptographic security claim'])
    save('SbfRuntimeTrace-coverage.json',summary)
except BaseException as exc:
    error=dict(type=type(exc).__name__,message=str(exc))
finally:
    receipt=dict(target='retained new trace, chain, native metadata and partial schema audit',exit=1 if error else 0,error=error,
        argv=getattr(sys,'orig_argv',sys.argv),argv_source='sys.orig_argv' if hasattr(sys,'orig_argv') else 'sys.argv',
        source_revision=json.loads((OUT/'SbfRuntimeTrace-transport-receipt.json').read_text())['source_revision'],
        checks=checks,wall_seconds=time.monotonic()-START,
        peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024),swap_operations=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,
        aggregate_rss='UNOBSERVED; small local data audit',axioms='N/A',python=dict(executable=sys.executable,version=sys.version,binary_pin=pin(Path(sys.executable).read_bytes())),
        inputs={p.name:pin(p.read_bytes()) for p in OUT.iterdir() if p.is_file() and p.name in ('SbfRuntimeTrace-transport.stdout','SbfRuntimeTrace-transport.stderr','SbfRuntimeTrace-transport-receipt.json','SbfRuntimeTrace-preregister.json','SbfRuntimeTrace-sourcepins.json')},
        sourcepins={p.name:pin(p.read_bytes()) for p in HERE.iterdir() if p.is_file()},
        dependencies={n:dict(file=getattr(m,'__file__',None),pin=pin(Path(m.__file__).read_bytes()) if getattr(m,'__file__',None) and Path(m.__file__).is_file() else None,body_binding='not implied by source hash') for n,m in sorted(sys.modules.items()) if m is not None})
    save('SbfRuntimeTrace-analysis-receipt.json',receipt)
    print(json.dumps(dict(exit=receipt['exit'],error=error,checks=len(checks))))
raise SystemExit(1 if error else 0)
