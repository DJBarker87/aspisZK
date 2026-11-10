#!/usr/bin/env python3
"""PCWO tool-build controller (host side, inside one admitted 6G/8G swap-0 scope). Newest Aeneas/Charon pair.
Phase 1 (native, this scope): Charon Rust release build (nightly-2026-09-17, toolchain used read-only via RUSTUP_TOOLCHAIN, CARGO_HOME in the workspace).
Phase 2 (container, image r3, cgroup capped 6G/8G swap 0 pids 64 as in PCWC_toolbuild_host.py, but network ENABLED and writable layer for opam):
charon-ml + Aeneas via PCWO_build_pair.sh. Deviations from the p4c recipe are recorded in PCWO_TOOL_BUILD.json."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,subprocess,time,os,shutil
E=Path(__file__).resolve().parent
run=sys.argv[1];spec=json.loads((E/(run+'_spec.json')).read_text());assert spec['run']==run
sha=lambda b:hashlib.sha256(b).hexdigest()
R=lambda a:subprocess.check_output(a,text=True).strip()
out=E/(run+'_out');out.mkdir(exist_ok=False);work=out/'work';work.mkdir();(out/'bin').mkdir()
rel=next(l.split(':',2)[2].strip().lstrip('/') for l in Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0:'))
scg=Path('/sys/fs/cgroup')/rel
want=spec['expected_limits'];got={n:(scg/n).read_text().strip() for n in want};assert got==want,(got,want)
t_all=time.monotonic();rec={'run':run,'scope_limits':got}
# ---- sources: git archive of the exact commits (clean trees), hashes recorded
for k in ('aeneas','charon'):
    src=Path(spec['src'][k]);head=R(['git','-C',str(src),'rev-parse','HEAD']);assert head==spec['rev'][k],(k,head)
    st=R(['git','-C',str(src),'status','--porcelain']);assert st=='',k
    tgz=out/(k+'-exact-source.tar.gz')
    subprocess.check_call(['git','-C',str(src),'archive','--format=tar.gz','-o',str(tgz),head])
    rec[k+'_archive_sha256']=sha(tgz.read_bytes());rec[k+'_revision']=head
    (work/k).mkdir();subprocess.check_call(['tar','xzf',str(tgz),'-C',str(work/k),'--no-same-owner'])
# PCWO: apply the two Aeneas patches (unified diffs against 0d21a9ec) to the unpacked aeneas tree; hashes recorded
rec['patches']={}
for pn in spec['patches']:
    pf=E/pn;rec['patches'][pn]=sha(pf.read_bytes())
    assert rec['patches'][pn]==spec['patch_sha256'][pn],pn
    subprocess.check_call(['patch','-p1','--no-backup-if-mismatch','-i',str(pf)],cwd=str(work/'aeneas'))
rec['patched_files_sha256']={f:sha((work/'aeneas'/f).read_bytes()) for f in spec['patched_files']}
# charon submodule crates/minirust (not in git archive): archive its pinned commit separately and unpack in place
sm=Path(spec['src']['charon'])/'crates'/'minirust';smh=R(['git','-C',str(sm),'rev-parse','HEAD']);assert smh==spec['rev']['charon_minirust'],smh
assert R(['git','-C',str(sm),'status','--porcelain'])==''
stgz=out/'minirust-exact-source.tar.gz';subprocess.check_call(['git','-C',str(sm),'archive','--format=tar.gz','-o',str(stgz),smh])
rec['minirust_archive_sha256']=sha(stgz.read_bytes());rec['minirust_revision']=smh
(work/'charon'/'crates'/'minirust').mkdir(parents=True,exist_ok=True);subprocess.check_call(['tar','xzf',str(stgz),'-C',str(work/'charon'/'crates'/'minirust'),'--no-same-owner'])
# aeneas/src/charon is a symlink to ../charon in the repo; the recipe's layout is /work/aeneas and /work/charon
# ---- phase 1: charon rust (or reuse of an earlier attempt's verified binaries when the spec names one)
if spec.get('reuse_rust_from'):
    old=Path(spec['reuse_rust_from']);orc=json.loads((old/'receipt.json').read_text())
    assert orc['charon_revision']==rec['charon_revision'] and orc['charon_archive_sha256']==rec['charon_archive_sha256'] and orc['minirust_archive_sha256']==rec['minirust_archive_sha256']
    for b in ('charon','charon-driver'):
        shutil.copy2(old/'bin'/b,out/'bin'/b);rec['sha256_'+b]=sha((out/'bin'/b).read_bytes());assert rec['sha256_'+b]==orc['sha256_'+b],b
    rec['rust_phase']=dict(reused_from=str(old),original=orc['rust_phase'])
else:
 env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_HOME=str(E/'PCWO_cargo_home'),CARGO_TARGET_DIR=str(out/'charon-target'),CARGO_BUILD_JOBS='3',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin')
 t0=time.monotonic()
 with (out/'rust-build.log').open('w') as lg:
     r=subprocess.run(['/usr/bin/time','-v','-o',str(out/'rust-build.time'),'timeout','1500','cargo','build','--release','--locked'],cwd=str(work/'charon'/'charon'),env=env,stdout=lg,stderr=subprocess.STDOUT)
 rec['rust_phase']=dict(exit=r.returncode,wall_seconds=round(time.monotonic()-t0,3),peak_scope_bytes=(scg/'memory.peak').read_text().strip(),swap=(scg/'memory.swap.current').read_text().strip(),events=(scg/'memory.events').read_text().replace('\n',' | '))
 tm=(out/'rust-build.time').read_text() if (out/'rust-build.time').exists() else ''
 rec['rust_phase']['max_rss_kib']=next((l.split(':',1)[1].strip() for l in tm.splitlines() if 'Maximum resident' in l),None)
 if r.returncode!=0:
     (out/'receipt.json').write_text(json.dumps(dict(rec,exit_status=r.returncode,phase='rust'),indent=2));print(json.dumps(rec));sys.exit(r.returncode)
 for b in ('charon','charon-driver'):
     shutil.copy2(out/'charon-target'/'release'/b,out/'bin'/b);rec['sha256_'+b]=sha((out/'bin'/b).read_bytes())
# ---- phase 2: container
name='pcwh-'+run.lower();img=spec['image']
(work/'build-pair.sh').write_bytes((E/'PCWO_build_pair.sh').read_bytes());rec['build_pair_sh_sha256']=sha((work/'build-pair.sh').read_bytes())
R(['docker','create','--name',name,'--pids-limit','64','--memory','8g','--memory-swap','8g','-v',str(work)+':/work','--entrypoint','bash',img,'/work/build-pair.sh'])
st=json.loads(R(['docker','inspect',name]))[0];assert st['Image']==img and st['State']['Status']=='created'
(out/'container-before.json').write_text(json.dumps(st,indent=2)+'\n')
R(['docker','start',name]);st=json.loads(R(['docker','inspect',name]))[0];pid=st['State']['Pid'];cid=st['Id']
crel=next(x.split(':',2)[2] for x in Path(f'/proc/{pid}/cgroup').read_text().splitlines() if x.startswith('0::'))
assert cid in crel,crel;cg=Path('/sys/fs/cgroup')/crel.lstrip('/')
cap={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
subprocess.check_call(['sudo','-n','systemctl','set-property','--runtime','docker-'+cid+'.scope','MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0'])
rd=lambda p:p.read_text().strip()
cgot={k:rd(cg/k) for k in cap};assert cgot==cap,cgot
pids=rd(cg/'pids.max')
(out/'preflight.json').write_text(json.dumps(dict(container=cid,image=img,cgroup=str(cg),limits=cgot,pids_max=pids,network='default bridge (ENABLED, deviation)',read_only=False),indent=2)+'\n')
(work/'aeneas-go').write_text('cgroup verified\n')
t1=time.monotonic();peak=0;last={};timedout=False
budget=2900-(time.monotonic()-t_all)
while True:
    s2=json.loads(R(['docker','inspect',name]))[0]
    if not s2['State']['Running']:break
    try:
        peak=max(peak,int(rd(cg/'memory.current')));last={k:rd(cg/k) for k in ['memory.current','memory.peak','memory.swap.current','memory.events']}
    except FileNotFoundError:pass
    if time.monotonic()-t1>budget:subprocess.call(['docker','stop','-t','5',name]);timedout=True;break
    time.sleep(1)
s2=json.loads(R(['docker','inspect',name]))[0];rc=s2['State']['ExitCode']
(out/'container-after.json').write_text(json.dumps(s2,indent=2)+'\n')
(out/'container.log').write_text(subprocess.run(['docker','logs',name],capture_output=True,text=True).stdout)
pl=work/'pair-build'
if (work/'pair-build.log').exists():shutil.copy2(work/'pair-build.log',out/'pair-build.log')
for f in pl.glob('*'):shutil.copy2(f,out/('pair-'+f.name))
rec['container_phase']=dict(exit=rc,wall_seconds=round(time.monotonic()-t1,3),sampled_cgroup_peak_bytes=peak,last_cgroup_observation=last,timeout_hit=timedout,limits=cgot)
b=work/'bin'/'aeneas'
if rc==0 and b.exists():
    shutil.copy2(b,out/'bin'/'aeneas');rec['sha256_aeneas']=sha(b.read_bytes())
rec['wall_seconds_total']=round(time.monotonic()-t_all,3);rec['exit_status']=rc
(out/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
rec['image_commit']=subprocess.run(['docker','commit',name,spec['commit_image']],capture_output=True,text=True).stdout.strip()  # NEW tag, keeps the opam switch for a second build scope
(out/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
subprocess.call(['docker','rm',name])
print(json.dumps(rec));sys.exit(rc)
