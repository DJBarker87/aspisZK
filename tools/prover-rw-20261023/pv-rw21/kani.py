"""One preflighted Kani harness; reuse real retained cache, exact filters."""
from pathlib import Path
import subprocess,json,shlex,sys,datetime
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw21-20261027';n=int(sys.argv[1]);plan=json.loads((e/'KANI-PLAN.json').read_text());harness=plan.get('replacement_route_after_timeouts',{}).get(str(n),plan['queue'][n-1]);solver=plan.get('solver_by_run',{}).get(str(n),plan['solver']);assert 1<=n<=10
h='dombarker@100.108.41.90';b='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023';src=b+'/src';name=f'pv-rw21-kani-{n:02d}'+('-retry'+sys.argv[2] if len(sys.argv)>2 else '');out=e/name;out.mkdir()
def ssh(c):return subprocess.run(['ssh',h,c],text=True,capture_output=True)
q=ssh('mkdir -p '+b+'/pv-rw21; python3 '+src+'/tools/prover-rw-20261023/native-entropy/reservation.py '+b+'/pv-rw21/'+name+'-admission.json > '+b+'/pv-rw21/'+name+'-admission.log 2>&1; pv_status=$?; cat '+b+'/pv-rw21/'+name+'-admission.log; exit $pv_status')
(out/'admission.log').write_text(q.stdout+q.stderr)
if q.returncode:print(q.stdout+q.stderr);sys.exit(78)
# Fail before charging on the known dangling-target configuration.
target=src+'/tools/prover-rw-20261023/pv-rw-step/proof/target'
q=ssh('test -d '+target+' && test ! -L '+target+' && test -x /home/dombarker/.cargo/bin/cargo && /home/dombarker/.cargo/bin/cargo kani --version');assert q.returncode==0,q.stderr
(out/'configuration.txt').write_text(q.stdout+'\nreal target directory: '+target+'\n'+json.dumps(plan,indent=2))
q=ssh('mkdir -p '+src+'/tools/prover-rw-20261023/pv-rw21/proof');assert q.returncode==0
for f in ['Cargo.toml','lib.rs','small.rs']:
 (out/(f+'.txt')).write_bytes((r/'tools/prover-rw-20261023/pv-rw21/proof'/f).read_bytes())
 subprocess.run(['scp',str(r/'tools/prover-rw-20261023/pv-rw21/proof'/f),h+':'+src+'/tools/prover-rw-20261023/pv-rw21/proof/'+f],check=True,capture_output=True)
q=ssh('cd '+src+' && /home/dombarker/.cargo/bin/cargo metadata --offline --no-deps --format-version 1 --manifest-path tools/prover-rw-20261023/pv-rw21/proof/Cargo.toml');assert q.returncode==0,q.stderr
(out/'metadata.json').write_text(q.stdout)
if solver=='kissat':
 q=ssh('/home/dombarker/.kani/kani-0.67.0/bin/kissat --version');assert q.returncode==0,q.stderr
 (out/'solver-version.txt').write_text(q.stdout+q.stderr)
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()
q=ssh('printf %s '+shlex.quote(rev+'+recorded-proof-inputs')+' > '+src+'/source-revision.txt');assert q.returncode==0
cmd=['python3','tools/prover-rw-20261023/run-host.py',name,'env','CARGO_TARGET_DIR='+target,'timeout','240','/home/dombarker/.cargo/bin/cargo','kani','--manifest-path','tools/prover-rw-20261023/pv-rw21/proof/Cargo.toml','--lib','--exact','--harness',harness,'--solver',solver,'--output-format','terse','--no-overflow-checks','-j','4','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
(out/'charge.json').write_text(json.dumps(dict(run=n,harness=harness,revision=rev,configuration_checked=True,command=cmd,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()),indent=2)+'\n')
q=ssh('cd '+src+' && PROVER_RW_RUSTFLAGS='+shlex.quote(plan.get('release_rustflags','-C link-arg=-Wl,--threads=4'))+' CT_EXPECTED='+shlex.quote(plan['expected_work']+'; '+harness)+' '+' '.join(map(shlex.quote,cmd)))
(out/'wrapper.log').write_text(q.stdout+q.stderr)
for f in ['receipt.json','preflight.json','time.log','stdout.log','stderr.log','reservation-at-barrier.json']:
 z=ssh('cat '+src+'/receipts/'+name+'/'+f);(out/f).write_text(z.stdout)
print(q.stdout[-2000:]+q.stderr[-2000:]);print((out/'stdout.log').read_text()[-3500:]);print((out/'stderr.log').read_text()[-2000:]);sys.exit(q.returncode)
