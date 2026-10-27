import os,json,pathlib,subprocess,time,hashlib,sys
B=pathlib.Path(__file__).resolve().parent
S=B.parent/'codex-cx-lowering2-20261026/src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
base=json.load(open(B/'ELa_historical.json'))
for f in base['source_checks']:
 assert sha(S/f['path'])==f['expected_sha256'],f
cg=pathlib.Path('/sys/fs/cgroup')/next(l.split(':',2)[2].strip().lstrip('/') for l in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0:'))
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64']))
for mode in ['default','devnet','pool']:
 out=B/('ELa_'+mode);out.mkdir(exist_ok=False)
 env=os.environ.copy()
 for k in list(env):
  if k.startswith(('CARGO_PROFILE_','ASPIS_')) or k in ['RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS']: env.pop(k)
 env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_HOME='/home/dombarker/.cargo',CARGO_TARGET_DIR=str(B/'ELa_target'),CARGO_NET_OFFLINE='true',CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4',RUSTC_WRAPPER=str(S.parent/'rustc-diagnostics.py'),S10_DIAGNOSTICS=str(out/'diagnostics'))
 if mode=='devnet':env.update(ASPIS_R1_POOL_PROGRAM_ID='BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs',ASPIS_R1_REGISTRY_PROGRAM_ID='9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q')
 old=next(x for x in base['builds'] if x['mode']==mode)
 cmd=list(old['command']['command']);cmd[cmd.index('--sbf-out-dir')+1]=str(out/'artifacts')
 rec=dict(mode=mode,command=cmd,cwd=str(S),env={k:v for k,v in env.items() if k.startswith(('CARGO_','RUST','S10_','ASPIS_')) or k=='PATH'},limits=limits,cgroup=str(cg),expected_sha256=old['artifact']['expected_sha256'],source_revision=base['source_revision'],print_axioms='N/A: SBF artifact replay')
 (out/'command.json').write_text(json.dumps(rec,indent=2)+'\n')
 start=time.monotonic()
 with (out/'stdout.log').open('w') as log:
  r=subprocess.run(['/usr/bin/time','-v','-o',str(out/'time.log'),'timeout','600',*cmd],cwd=S,env=env,stdout=log,stderr=subprocess.STDOUT)
 rec.update(exit_status=r.returncode,wall_seconds=time.monotonic()-start,cgroup_memory_peak_bytes=(cg/'memory.peak').read_text().strip())
 tim=(out/'time.log').read_text()
 for key,label in [('peak_rss_kib','Maximum resident set size'),('swaps','Swaps')]:rec[key]=next((l.split(':',1)[1].strip() for l in tim.splitlines() if label in l),None)
 name='aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so'; artifact=out/'artifacts'/name
 if artifact.exists():rec.update(sha256=sha(artifact),bytes=artifact.stat().st_size,byte_identical=sha(artifact)==rec['expected_sha256'])
 (out/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n'); print(json.dumps(rec),flush=True)
 if r.returncode:sys.exit(r.returncode)
