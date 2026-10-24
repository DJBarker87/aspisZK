#!/usr/bin/env python3
"""Focused offline consistency audit; no host access, proof or compilation."""
import ast,hashlib,json,pathlib,resource,subprocess,sys,time
T=pathlib.Path(__file__).resolve().parent;R=T.parents[1];E=R/'evidence/sbf-cache-prep-20261024';BASE='555248fcfe2db2e8de4e6aaaa191c9eaa6539426';start=time.monotonic();checks=[];inputs=[];exit_code=0

def sha(b):return hashlib.sha256(b).hexdigest()
def load(name):return json.loads((E/name).read_text())
def check(name,ok,count=1):
    checks.append(dict(check=name,passed=bool(ok),records=count));assert ok,name

def script_pin(pin):return [p for p in sorted(T.iterdir()) if p.is_file() and sha(p.read_bytes())==pin]
try:
    for folder in (T,E):
        for p in sorted(folder.iterdir()):
            if p.name=='audit.json':continue
            check('regular bounded text '+p.name,p.is_file() and not p.is_symlink() and p.stat().st_size<=5000000)
            b=p.read_bytes();check('no binary '+p.name,b'\0' not in b);inputs.append(dict(path=str(p.relative_to(R)),sha256=sha(b),bytes=len(b)))
            if p.suffix=='.py':ast.parse(b,filename=str(p))
    for phase in ['proc-v1','proc','metadata','inventory','registry','registry-focused','export-pre','export','export-post','runtime']:
        tr=load(phase+'.transport.json');out=(E/(phase+'.stdout.json')).read_bytes();err=(E/(phase+'.stderr.txt')).read_bytes();x=json.loads(out)
        check(phase+' exact output/exit/zeroSwap',tr['exit']==x['receipt']['exit']==0 and tr['stdout_sha256']==sha(out) and tr['stderr_sha256']==sha(err) and x['receipt']['swaps']==tr['swaps']==0)
        check(phase+' retained exact executed scripts',bool(script_pin(tr['script_sha256'])) and bool(script_pin(tr['transport_sha256'])))
        check(phase+' bounded host process RSS',x['receipt']['peak_rss_kib']<512*1024)
    check('initial denied observation preserved',not load('proc-v1.stdout.json')['allowed_to_enter'] and not load('proc-v1.stdout.json')['process_set_stable'])
    for phase in ['proc','export-pre','export-post']:
        x=load(phase+'.stdout.json');rows=x['processes']
        check(phase+' complete stable visible no donor matches',x['allowed_to_enter'] and x['initial_pids']==x['final_pids'] and all(r['identity_stable'] and not r['errors'] and not r['matches'] for r in rows),len(rows))
        check(phase+' explicit kernel classification',all(r['identity']['flags']&0x200000 and r['cmdline_bytes']==0 for r in rows if r.get('classification')=='kernel-thread'))
    root_ast=ast.parse((T/'SbfCachePrep_proc.py').read_text())
    imports=[a.name for n in ast.walk(root_ast) if isinstance(n,ast.Import) for a in n.names]
    check('root helper no subprocess/network imports',set(imports)<={'hashlib','json','os','pathlib','resource','sys','time'})
    check('root helper no mutation/exec calls',not any(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr in {'write','write_text','write_bytes','unlink','chmod','chown','mkdir','rename','execv','execve','system','popen'} for n in ast.walk(root_ast)))
    check('root file opens read-only',all(n.args and isinstance(n.args[0],ast.Constant) and n.args[0].value=='rb' for n in ast.walk(root_ast) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='open'))
    rows=load('inventory.json');index={r['path']:r for r in rows};snap=load('snapshot-manifest.json');ex=load('export.stdout.json');inv=load('inventory.stdout.json')
    check('complete inventory counts/no keys or unsafe types',len(index)==len(rows)==5501 and sum(r['type']=='regular' for r in rows)==4617 and all(r['type'] in ('regular','directory') and not r.get('excluded') for r in rows) and not inv['excluded'],len(rows))
    check('inventory digest matches new acquired pin',sha((E/'inventory.json').read_bytes())=='e98de11bf81d5497652882f2663c6eedec3a0aa13a3ae14877f79da946b07541')
    check('snapshot complete regular set',{r['path'] for r in snap}=={r['path'] for r in rows if r['type']=='regular'} and len(snap)==4617)
    check('all snapshot hashes/sizes/modes and independent inode/linkcount',all(r['sha256']==index[r['path']]['sha256'] and r['bytes']==index[r['path']]['bytes'] and r['mode']==index[r['path']]['mode'] and r['destination_nlink']==1 and (r['source_device'],r['source_inode'])!=(r['destination_device'],r['destination_inode']) for r in snap),len(snap))
    check('copy full pre/copy/post and exact space reservation',ex['copied'] and ex['source_pre_copy_post_equal'] and ex['bytes']==sum(r['bytes'] for r in snap)==1185157546 and ex['space_before']>ex['bytes']+1024**3)
    check('snapshot raw manifest pin',sha((E/'snapshot-manifest.json').read_bytes())==ex['output']['sha256'])
    for name,receipt in [('inventory.json',inv['outputs'][0]),('provenance.json',inv['outputs'][1]),('registry-join.json',load('registry.stdout.json')['output']),('registry-focused-join.json',load('registry-focused.stdout.json')['output'])]:
        check('collected exact '+name,sha((E/name).read_bytes())==receipt['sha256'] and (E/name).stat().st_size==receipt['bytes'])
    original=load('registry-join.json')['packages'];focused=load('registry-focused-join.json')['packages'];final={r['crate']:r for r in original};final.update({r['crate']:r for r in focused})
    check('registry exact scoped retest',len(original)==123 and sum(r['verified'] for r in original)==115 and {r['crate'] for r in focused}=={r['crate'] for r in original if not r['verified']})
    check('all published archives match frozen lock',all(r['archive_sha256']==r['lock_checksum'] for r in final.values()),123)
    check('121 exact source sets and two precise extra-name denials',sum(r['verified'] for r in final.values())==121 and {r['crate'] for r in final.values() if not r['verified']}=={'serde_core-1.0.228','version_check-0.9.5'} and all(not r['consumed_missing'] and r['error']=='unexpected unpacked sources' for r in final.values() if not r['verified']))
    check('concrete source/fingerprint provenance retained',len(load('provenance.json')['fingerprints'])==662 and len(load('provenance.json')['dep_info'])==586 and load('registry-focused.stdout.json')['rustc_info'][0]['version_answers'])
    for name in ['synthetic-proc-tests.json','guard-tests.json']:
        x=load(name);check(name+' all offline tests pass',all(c['passed'] for c in x['checks']) and x['receipt']['exit']==0 and x['receipt']['swaps']==0,len(x['checks']))
        check(name+' exact tested inputs',all(sha((T/p).read_bytes())==s for p,s in x['dependencies'].items()))
    md=load('metadata.stdout.json');runtime=load('runtime.stdout.json')
    check('path ownership and no symlink ancestors',all(not q['symlink'] for r in md['paths'] for q in r['chain']) and md['paths'][0]['chain'][-1]['uid']==1000 and md['paths'][0]['chain'][-1]['mode']=='0o700')
    check('official cargo metadata-only exact version',md['cargo_query']['stdout']=='cargo 1.89.0 (ca74c32f0 2025-10-17)\n' and md['cargo_query']['exit']==0)
    check('reference interpreter and public loaded runtime pinned',runtime['executable']=='/usr/bin/python3' and any(r['path']=='/usr/bin/python3' and r['sha256']=='e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f' for r in runtime['files']) and any('libz.so' in r['path'] for r in runtime['files']))
    old=json.loads(subprocess.check_output(['git','show',BASE+':evidence/sbf-recapture-prep-20261024/future-plan.json']));plan=load('future-plan.json')
    check('exact three reviewed commands retained',len(plan['builds'])==3 and all(all(a[k]==b[k] for k in ['command','environment','unset_environment','scope_command','cwd','output','linked_output','expected_sha256','historical_predecessor']) for a,b in zip(old['builds'],plan['builds'])))
    pins=['f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548']
    check('all three current ELF pins unchanged',pins==[r['expected_sha256'] for r in plan['builds']])
    check('all execution remains blocked',plan['builds_run']==plan['resources']['scope_launches']==0 and plan['execution_blockers'] and plan['headroom'].startswith('UNKNOWN') and all(b['status'].startswith('PREPARED NOT RUN') for b in plan['builds']))
    for mode in ['default','devnet','pool']:
        cmd=[sys.executable,'-B',str(T/'SbfCachePrep_runner.py'),mode,'--run'];t=time.monotonic();r=subprocess.run(cmd,capture_output=True)
        check('runner denies '+mode,r.returncode==2 and b'DENIED' in r.stderr)
        checks[-1].update(command=cmd,exit=r.returncode,wall_seconds=time.monotonic()-t,stdout_sha256=sha(r.stdout),stderr_sha256=sha(r.stderr))
    for folder in ['tools/sbf-recapture-prep-20261024','evidence/sbf-recapture-prep-20261024']:
        paths=subprocess.check_output(['git','ls-tree','-r','--name-only',BASE,'--',folder],text=True).splitlines()
        for path in paths:
            b=subprocess.check_output(['git','show',BASE+':'+path]);inputs.append(dict(path=path,revision=BASE,sha256=sha(b),bytes=len(b),assessment='REUSED immutable prior evidence, no new archive/source/ELF gate'))
    changed=subprocess.check_output(['git','diff','--name-only',BASE],text=True).splitlines()+subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True).splitlines()
    check('assigned paths and branch only',all(p.startswith(('tools/sbf-cache-prep-20261024/','evidence/sbf-cache-prep-20261024/')) for p in changed) and subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/cx-sbf-cache-prep-20261024')
except Exception as e:
    exit_code=1;checks.append(dict(passed=False,error=type(e).__name__+': '+str(e)))
u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
interpreter=pathlib.Path(sys.executable);direct=[]
for module in tuple(sys.modules.values()):
    name=getattr(module,'__file__',None)
    if name and pathlib.Path(name).is_file():direct.append(dict(module=module.__name__,path=name,sha256=sha(pathlib.Path(name).read_bytes())))
result=dict(schema='SbfCachePrep-focused-offline-audit-v1',checks=checks,check_groups=len(checks),ordered_inputs=inputs,ordered_inputs_sha256=sha(json.dumps(inputs,sort_keys=True).encode()),budgets={k:0 for k in ['lean','kani','rust','compiler','build','extraction','backend','elf_gate','consumer','full_manifest','scope']},runtime=dict(executable=str(interpreter),sha256=sha(interpreter.read_bytes()),version=sys.version,direct_modules=direct,loaded_DSO_limit='macOS shared-cache mappings not separately sealed; no compiler/runtime trust closure claim'),receipt=dict(command=[sys.executable,'-B',str(pathlib.Path(__file__).resolve())],exit=exit_code,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,children_peak_rss_bytes=c.ru_maxrss,swaps=u.ru_nswap+c.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=sha(pathlib.Path(__file__).read_bytes()),print_axioms='N/A: no theorem/import/proof/compiler/build gate'))
with (E/'audit.json').open('x') as f:json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(dict(groups=len(checks),receipt=result['receipt'],failure=checks[-1] if exit_code else None),indent=2));sys.exit(exit_code)
