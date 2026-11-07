"""Frozen SBF replay in PCH cache; retained inputs read-only, no cargo/key use."""
import pathlib,subprocess,json,hashlib,shutil,lzma,os,sys,time
B=pathlib.Path(__file__).resolve().parent;a=sys.argv[1];I=json.loads((B/'PCH_BUILD_INPUT.json').read_text());D=I['deployed'];S=B/'src';S.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cg=pathlib.Path('/sys/fs/cgroup')/pathlib.Path('/proc/self/cgroup').read_text().split('0::')[1].strip().lstrip('/')
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']};assert list(limits.values())==['6442450944','8589934592','0','64']
assert shutil.disk_usage(B).free>=40_000_000_000
sources=json.loads(lzma.decompress((B/'PCH_FROZEN.json.xz').read_bytes()));pins={}
for n,v in sources.items():
 p=S/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(v);pins[n]=sha(p)
assert pins['Cargo.lock']==D['lock_sha256']
for c in D['compiler_input_checks']:assert pins[c['path']]==c['expected'],c['path']
# This retained dependency workspace is explicitly cited by the exact-ELF receipt.
old=pathlib.Path('/home/dombarker/project-offloads/codex-cx-lowering2-20261026/sbf-target-pool')
inputs=[]
for rel in ['sbpf-solana-solana/release/deps','release/deps']:
 dest=B/'deps'/rel;dest.mkdir(parents=True,exist_ok=True)
 for p in sorted((old/rel).glob('*')):
  if p.suffix not in ['.rlib','.rmeta','.so']:continue
  if 'aspis_pool' in p.name:continue
  q=dest/p.name;h=sha(p)
  if q.exists():assert sha(q)==h
  else:shutil.copyfile(p,q)
  assert sha(q)==h
  inputs.append(dict(source=str(p),copy=str(q),sha256=h,bytes=q.stat().st_size))
rec=dict(attempt=a,expected_work='optimized SBF Pool compilation/linking using copied retained unchanged dependencies',source_pins=pins,copied_inputs=inputs,limits=limits,lock_before=pins['Cargo.lock'],source_revisions=dict(pool=D['frozen_revision'],crates=D['crates_revision']),resolved_packages=D['pool_build']['resolved_packages'],resolved_packages_source='retained exact-build cargo metadata; compiler cfg lists separately authoritative',compiler_features={})
for c,cmd in I['commands'].items():rec['compiler_features'][c]=[cmd[i+1] for i,x in enumerate(cmd[:-1]) if x=='--cfg']
cmd=I['commands']['aspis_pool'];assert sha(pathlib.Path(cmd[0]))=='d95c95b68e321ad76634e1fd26b0a7c20ccdbae9ad9ca733f3ae2f2b4a0b6002'
out=B/a;out.mkdir(exist_ok=False)
new=[]
for x in cmd:
 for root in ['/home/dombarker/project-offloads/codex-cx-legacy-removal-20261109/target',str(old)]:
  x=x.replace(root,str(B/'deps'))
 new.append(x)
i=new.index('--out-dir');new[i+1]=str(out)
rec['command']=new;rec['compiler_sha256']=sha(pathlib.Path(new[0]));rec['disk_free_before_bytes']=shutil.disk_usage(B).free
(B/(a+'_INPUTS.json')).write_text(json.dumps(rec,indent=1)+'\n')
t=time.monotonic();env=os.environ.copy();env.update(CARGO_NET_OFFLINE='true')
with (out/'compiler.stdout').open('w') as o,(out/'compiler.stderr').open('w') as e:r=subprocess.run(new,cwd=S,env=env,stdout=o,stderr=e)
rec.update(exit_status=r.returncode,wall_seconds=time.monotonic()-t,lock_after=sha(S/'Cargo.lock'),cgroup_peak_bytes=(cg/'memory.peak').read_text().strip())
if r.returncode==0:
 elf=out/'libaspis_pool.so';strip='/home/dombarker/.cache/solana/v1.52/platform-tools/llvm/bin/llvm-objcopy';rec['objcopy_sha256']=sha(pathlib.Path(strip))
 r=subprocess.run([strip,'--strip-all',str(elf),str(out/'aspis_pool.so')],capture_output=True,text=True);rec['strip_exit']=r.returncode
 rec['elf_sha256']=sha(out/'aspis_pool.so');rec['elf_matches']=rec['elf_sha256']=='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc'
rec['artifacts']=[]
for p in out.iterdir():
 if p.is_file():
  rec['artifacts'].append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
  if p.suffix in ['.ll','.mir'] or p.name.startswith('compiler.'):
   q=B/(a+'_'+p.name+'.xz');q.write_bytes(lzma.compress(p.read_bytes()));rec['artifacts'][-1]['compressed']=str(q)
(B/(a+'_BUILD.json')).write_text(json.dumps(rec,indent=1)+'\n')
assert rec['lock_before']==rec['lock_after']
print(json.dumps({k:rec.get(k) for k in ['attempt','exit_status','elf_sha256','elf_matches','wall_seconds']}))
assert rec['exit_status']==0
assert rec.get('elf_matches'), 'Authority gate: ELF mismatch'
