from pathlib import Path
import os,subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rows10b-20261029')
O=D.parent/'codex-pv-ownd-20261029';P=O/'target/release/deps'
old=D.parent/'codex-pv-rows10-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for p in json.loads((old/'dependency-source-pins.json').read_text()):assert sha(Path(p['path']))==p['sha256']
units=json.loads((O/'deployed-units.json').read_text())
u=next(u for u in units if u['package_id'].endswith('#getrandom@0.3.4') and u['target']['name']=='getrandom')
assert u['features']==['std'] and u['profile']['opt_level']=='3'
assert not u['profile']['debug_assertions'] and not u['profile']['overflow_checks']
lib=P/'libgetrandom-fe336fb2b7d63711.rlib';libc=next(P.glob('liblibc-*.rlib'))
# Existing deployed dependency artifacts are checked against the prior receipt.
prior=json.loads((old/'native-result.json').read_text())
for p in [lib,libc]:assert sha(p)==next(x['sha256']for x in prior['inputs']if x['path']==str(p))
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'])
common=['rustc','+1.94.1','--edition=2021','-O','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind','--extern','libc='+str(libc),'-L','dependency='+str(P)]
commands=[common+['--extern','getrandom='+str(lib),str(D/'dispatch-native.rs'),'-o',str(D/'dispatch-native')],common+['--crate-type','cdylib',str(D/'interposer.rs'),'-o',str(D/'interposer.so')]]
print('Expected time: compilation/link of two tiny optimized harnesses, then four 64-byte source calls; no proof generation or dense arithmetic',flush=True)
for c in commands:subprocess.run(c,env=env,check=True)
runs=[]
for preloaded in [False,True]:
 e=env.copy();e.pop('LD_PRELOAD',None)
 if preloaded:e['LD_PRELOAD']=str(D/'interposer.so')
 q=subprocess.run([str(D/'dispatch-native')],env=e,text=True,capture_output=True,check=True)
 j=json.loads(q.stdout);j['controlled_preload']=preloaded;runs.append(j)
 if preloaded:
  assert j['probe_count']==1 and j['draw_count']==2
  assert not j['first_ok'] and not j['second_ok']
  assert j['first_errno']==5 and j['second_errno']==5
  assert j['first_changed'] and j['second_changed']
print(json.dumps(runs),flush=True)
r=dict(commands=commands,toolchain=subprocess.check_output(['rustc','+1.94.1','-Vv'],text=True,env=env),getrandom_unit=u,features_all_crates=[dict(package_id=x['package_id'],features=x['features'],profile=x['profile'])for x in units],runs=runs,inputs=[dict(path=str(p),sha256=sha(p))for p in [lib,libc,O/'deployed-units.json',O/'deployed-client-Cargo.lock',D/'dispatch-native.rs',D/'interposer.rs',D/'dispatch-native.py']],artifacts=[dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)for p in [D/'dispatch-native',D/'interposer.so']],evidence_class='finite controlled-loader validation of original deployed-configuration getrandom dependency; not shipped-client execution or an honest-witness privacy counterexample',conclusion='The cached dlsym target can be an interposed non-syscall function whose successful zero-length probe does not certify syscall provenance.',retained='V370 and actual deployment loader/cache identity remain P obligations; T unchanged')
(D/'dispatch-native-result.json').write_text(json.dumps(r,indent=2)+'\n')
