import pathlib,subprocess,json,sys,time,hashlib,runpy,os
ROOT=pathlib.Path('/home/dombarker/project-offloads/codex-pv-kscan-20261028')
SCANNER='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py'
name=sys.argv[1];graph_only=sys.argv[2:]==['graphs'];out=ROOT/name;out.mkdir(exist_ok=True)
if sys.argv[2:] in (['inner'],['inner-graphs']):
 cg=pathlib.Path('/sys/fs/cgroup'+pathlib.Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
 limits={k:(cg/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max','pids.max']}
 assert limits=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},limits
 r=runpy.run_path(SCANNER)['admission'](requested=0);(out/'barrier.json').write_text(json.dumps(r,indent=2));
 if not r.get('allowed'):sys.exit(78)
 cmd=['/home/dombarker/.cargo/bin/cargo','kani','--manifest-path',str(out/'package/Cargo.toml'),'--lib','--only-codegen','--keep-temps','--output-format','terse','-j','4']
 env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_TARGET_DIR=str(out/'target'))
 if sys.argv[2:]==['inner-graphs']:
  sys.exit(subprocess.run(['python3',str(ROOT/'goto_scan.py'),str(out)]).returncode)
 start=time.monotonic()
 with (out/'output.log').open('w') as f:p=subprocess.run(['/usr/bin/time','-v','-o',str(out/'time.log'),'timeout','180',*cmd],env=env,stdout=f,stderr=subprocess.STDOUT)
 (out/'receipt.json').write_text(json.dumps(dict(target=cmd,exit=p.returncode,wall_seconds=time.monotonic()-start,limits=limits,source_revision=json.loads((ROOT/'heads.json').read_text()),expected_phase='optimized diagnostic code generation only; no SAT proof and no restored credit',print_axioms='N/A; no Lean'),indent=2)+'\n');
 if p.returncode==0:subprocess.run(['python3',str(ROOT/'goto_scan.py'),str(out)],check=True)
 sys.exit(p.returncode)
for i in range(10):
 r=runpy.run_path(SCANNER)['admission'](requested=8*2**30);(out/f'admission-{i}.json').write_text(json.dumps(r,indent=2)+'\n')
 if r.get('allowed'):break
 print('REFUSED',i,flush=True);time.sleep(180)
else:sys.exit(78)
cmd=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',__file__,name,'inner-graphs' if graph_only else 'inner']
p=subprocess.run(cmd);sys.exit(p.returncode)
