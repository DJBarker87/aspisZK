import pathlib, hashlib, json, subprocess, os, re, sys
root = pathlib.Path('/home/dombarker/project-offloads/aspis-r440-native-fixture-candidate-20261003-a')
tool = pathlib.Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
rel = next(x.split('::', 1)[1].lstrip('/') for x in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
cg = pathlib.Path('/sys/fs/cgroup') / rel
def cgroup():
    return {n: (cg/n).read_text().strip() for n in ('memory.high','memory.max','memory.swap.max','pids.max','memory.peak','memory.swap.peak','memory.events')}
before = cgroup()
assert {k: before[k] for k in ('memory.high','memory.max','memory.swap.max','pids.max')} == {'memory.high':'5368709120','memory.max':'7516192768','memory.swap.max':'0','pids.max':'128'}
assert not root.exists(), 'fresh baseline root required'
assert subprocess.check_output(['git','rev-parse','HEAD'], cwd=tool, text=True).strip() == 'cb50ff16b9f1066b8a97dc06da704de2da2fa41c'
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=tool,text=True).strip()
assert sha(tool/'bin/charon') == 'b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c'
assert sha(tool/'bin/charon-driver') == '4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938'
heavy = [x for x in subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines() if len(x.split())>1 and x.split()[1] in ('rustc','cargo','charon','charon-driver','aeneas','lean','lean4')]
assert not heavy, heavy
mem = {k:v.strip() for k,v in (x.split(':',1) for x in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
cap = 7*1024**3
safe = min(40*1024**3, int(mem['MemTotal'].split()[0])*1024-16*1024**3)
assert int(mem['MemAvailable'].split()[0])*1024-cap >= 24*1024**3
reservations=[]
for user in (True, False):
    prefix=['systemctl']+(['--user'] if user else [])
    units=subprocess.check_output(prefix+['list-units','--all','--plain','--state=running','--no-legend'],text=True)
    for line in units.splitlines():
        name=line.split()[0]
        if not name.startswith('aspis') or not name.endswith(('.service','.scope')) or name=='aspis-r440-native-fixture-candidate.service': continue
        props=dict(x.split('=',1) for x in subprocess.check_output(prefix+['show',name,'-p','MemoryMax','-p','MemoryCurrent','-p','ControlGroup'],text=True).splitlines() if '=' in x)
        assert props['MemoryMax'].isdigit(), ('uncapped Aspis reservation',name,props)
        reservations.append({'unit':name,'user':user,**props})
assert cap+sum(int(x['MemoryMax']) for x in reservations) <= safe
rustc='/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc'
version=subprocess.check_output([rustc,'-Vv'],text=True)
assert '14210df0e27ccd7d9e6a05b8085cbd438e4bbc65' in version
candidate=pathlib.Path('/home/dombarker/project-offloads/aspis-r440-mono-closure-binding-20261003-a')
assert sha(candidate/'observer-bin/charon-driver')=='36cd66adb952d877a5ca6e17949fc4685525ed643d1b1fa7e92792d9a1d26625'
assert sha(candidate/'observer-bin/charon')=='b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c'
assert sha(candidate/'charon/src/bin/charon-driver/main.rs')=='afc8d62e3b0097805f9688653a0e435d54ea65c5c8ba3e698eb46a4fd16c49f5'
assert sha(candidate/'charon/src/bin/charon-driver/translate/translate_closures.rs')=='93d29b0184be8503aafd8884f13f56eb73ea4f5eacdecb751bed5a28cc3fd5ed'
fixture=json.loads(sys.argv[1])
root.mkdir(); (root/'captured_gamma.rs').write_text(fixture['source']); (root/'rustc-output').mkdir()
assert sha(root/'captured_gamma.rs')==fixture['sha256']
command=[str(candidate/'observer-bin/charon'),'rustc','--preset','aeneas','--mir','built','--monomorphize','--sysroot','default','--start-from','crate::gamma_step','--dest-file',str(root/'baseline.llbc'),'--','--edition=2024','--crate-type=lib','--crate-name','r440_captured_gamma','-C','opt-level=3','-C','overflow-checks=on','--out-dir',str(root/'rustc-output'),str(root/'captured_gamma.rs')]
record={'command':command,'source_revision':fixture['revision'],'fixture_sha256':fixture['sha256'],'pinned_tool_revision':'cb50ff16b9f1066b8a97dc06da704de2da2fa41c','wrapper_sha256':sha(tool/'bin/charon'),'driver_sha256':sha(candidate/'observer-bin/charon-driver'),'original_driver_sha256':sha(tool/'bin/charon-driver'), 'candidate_overlay_sha256':{'main':'afc8d62e3b0097805f9688653a0e435d54ea65c5c8ba3e698eb46a4fd16c49f5','translate_closures':'93d29b0184be8503aafd8884f13f56eb73ea4f5eacdecb751bed5a28cc3fd5ed'},'rustc':version,'effective_cgroup_before':before,'meminfo':mem,'reservations':reservations,'working_directory':str(root),'formal_axioms':'N/A diagnostic extraction'}
(root/'command.json').write_text(json.dumps(record,indent=2)+'\n')
env={**os.environ,'PATH':'/home/dombarker/.cargo/bin:'+os.environ.get('PATH',''),'RUSTUP_TOOLCHAIN':'nightly-2026-06-01'}
with (root/'stdout.log').open('wb') as out, (root/'stderr.log').open('wb') as err:
    run=subprocess.run(['/usr/bin/time','-v','-o',str(root/'gnu-time.txt'),*command],cwd=root,env=env,stdout=out,stderr=err)
assert sha(candidate/'observer-bin/charon-driver')==record['driver_sha256']
assert sha(tool/'bin/charon-driver')==record['original_driver_sha256'] and sha(tool/'bin/charon')==record['wrapper_sha256']
assert sha(root/'captured_gamma.rs')==fixture['sha256']
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=tool,text=True).strip()
txt=(root/'gnu-time.txt').read_text()
def metric(p):
    m=re.search(p,txt,re.M);return m.group(1).strip() if m else None
llbc=root/'baseline.llbc'
result={**record,'exit_status':run.returncode,'wall_time':metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(.+)'),'peak_rss_kib':int(metric(r'Maximum resident set size \(kbytes\):\s*(\d+)') or 0),'swaps':int(metric(r'Swaps:\s*(\d+)') or 0),'target_exists':llbc.exists(),'target_sha256':sha(llbc) if llbc.exists() else None,'has_errors':json.loads(llbc.read_text()).get('has_errors') if llbc.exists() else None,'effective_cgroup_after':cgroup()}
(root/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('exit_status','wall_time','peak_rss_kib','swaps','target_exists','target_sha256','has_errors')}))
raise SystemExit(run.returncode)
