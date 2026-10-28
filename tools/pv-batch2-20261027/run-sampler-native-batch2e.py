"""One optimized, capped, finite sampler differential; no source rewrite."""
from pathlib import Path
import subprocess,json,hashlib,shlex,sys
E=Path('evidence/pv-batch2-20261027/batch2e');H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-batch2-20261027';T=Path('tools/pv-batch2-20261027')
r=subprocess.run([sys.executable,str(T/'admission-probe-batch2e.py')],capture_output=True,text=True)
if r.returncode: print('admission held; no upload or native compiler launch');raise SystemExit(r.returncode)
paths=['crates/aspis-r1-cost-probe/src/sampler.rs','crates/aspis-r1-cost-probe/src/host_sampler.rs','crates/aspis-core/src/field/wide_exact.rs','crates/aspis-core/src/field/ct.rs','crates/aspis-core/src/field.rs']
expected={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in paths}
code='''from pathlib import Path
import hashlib,json
D=Path(DIR);expected=EXPECTED
r={p:hashlib.sha256((D/'candidate/src'/p).read_bytes()).hexdigest() for p in expected}
assert r==expected,(r,expected)
(D/'batch2e-sampler-native').mkdir(exist_ok=True)
print(json.dumps(dict(expected=expected,actual=r,matched=True)))
'''.replace('DIR',repr(D)).replace('EXPECTED',repr(expected))
r=subprocess.run(['ssh',H,'python3 -c '+shlex.quote(code)],capture_output=True,text=True,check=True);(E/'NATIVE-SOURCE-PINS.json').write_text(r.stdout)
for src,dst in [('sampler-native-batch2e.rs','batch2e-sampler-native/main.rs'),('sampler-native-batch2e.Cargo.toml','batch2e-sampler-native/Cargo.toml'),('sampler-native-batch2e.py','sampler-native-batch2e.py')]:subprocess.run(['scp','-q',str(T/src),H+':'+D+'/'+dst],check=True)
label='batch2e-sampler-differential-001'
cmd=shlex.join(['python3',D+'/native.py','candidate',label,'python3',D+'/sampler-native-batch2e.py'])
r=subprocess.run(['ssh',H,cmd],capture_output=True,text=True);(E/'NATIVE-LAUNCHER.log').write_text(r.stdout+r.stderr)
for src,dst in [('receipt/receipt.json','NATIVE-RECEIPT.json'),('receipt/stdout.log','NATIVE-OUT.log'),('receipt/stderr.log','NATIVE-ERR.log'),('receipt/time.log','NATIVE-TIME.log'),('admission-barrier.json','NATIVE-ADMISSION.json'),('reservation.log','NATIVE-RESERVATION.log')]:
 q=subprocess.run(['ssh',H,'cat '+D+'/candidate/'+label+'/'+src],capture_output=True,text=True)
 if q.returncode==0:(E/dst).write_text(q.stdout)
print('native launcher exit',r.returncode);print((E/'NATIVE-OUT.log').read_text() if (E/'NATIVE-OUT.log').exists() else 'no compiler receipt; inspect refusal')
raise SystemExit(r.returncode)
