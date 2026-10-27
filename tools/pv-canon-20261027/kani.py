from pathlib import Path
import sys,subprocess,json,shlex,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-canon-20261027';H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-canon-20261027';n=int(sys.argv[1]);assert 1<=n<=6
names=['op121_block_indices','op121_descending_blocks','interpolation_sample_ctor','interpolation_basis_indices','semantic_round_tags','sampler_word_indices'];name=names[n-1]
tp=E/'tally.json';t=json.loads(tp.read_text());assert t['kani']==n-1
subprocess.run(['ssh',H,'mkdir -p '+D+'/control/src'],check=True)
for f in ['Cargo.toml','src/lib.rs']:subprocess.run(['scp',str(R/'tools/pv-canon-20261027/control'/f),H+':'+D+'/control/'+f],check=True,stdout=subprocess.DEVNULL)
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
code='''from pathlib import Path
import subprocess,json,time,os
D=Path(DIR);O=D/'receipts'/NAME;O.mkdir(exist_ok=False)
G=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy')
a=subprocess.run(['python3',str(G/'reservation.py'),str(O/'reservation.json')],stdout=open(O/'reservation.log','w'),stderr=subprocess.STDOUT)
if a.returncode:print((O/'reservation.log').read_text());raise SystemExit(a.returncode)
cmd=['timeout','180','taskset','--cpu-list','0-3','/home/dombarker/.cargo/bin/cargo','kani','--exact','--harness',HARNESS,'-j','4','--output-format','terse','--cbmc-args','--unwinding-assertions']
env=os.environ.copy();env.update(PATH='/home/dombarker/.cargo/bin:'+env['PATH'],CARGO_BUILD_JOBS='4',CARGO_PROFILE_DEV_OPT_LEVEL='3')
start=time.monotonic();a=subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(G/'barrier.py'),str(O/'barrier.json'),'/usr/bin/time','-v','-o',str(O/'time.log'),*cmd],cwd=D/'control',env=env,stdout=open(O/'out.log','w'),stderr=subprocess.STDOUT)
r=dict(target=HARNESS,exit=a.returncode,wall_seconds=time.monotonic()-start,revision=REVISION,phase='optimized tiny control/indexing model, no field arithmetic',print_axioms='N/A Kani',time_log=(O/'time.log').read_text() if (O/'time.log').exists() else None);(O/'receipt.json').write_text(json.dumps(r,indent=2));print((O/'out.log').read_text());print(json.dumps(r))
'''.replace('DIR',repr(D)).replace('NAME',repr('kani'+str(n))).replace('HARNESS',repr(name)).replace('REVISION',repr(rev))
a=subprocess.run(['ssh',H,'python3 -'],input=code,text=True,capture_output=True);print(a.stdout+a.stderr);(E/f'kani{n}-launcher.log').write_text(a.stdout+a.stderr)
subprocess.run(['scp','-r',H+':'+D+'/receipts/kani'+str(n),str(E)],stdout=subprocess.DEVNULL)
r=E/f'kani{n}/receipt.json'
if r.exists() and json.loads(r.read_text())['time_log'] is not None:t['kani']+=1;tp.write_text(json.dumps(t,indent=2)+'\n')
else: print('UNCHARGED: reservation wait 180s')
