from pathlib import Path
import subprocess,hashlib,json,tomllib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rows10-20261029'
paths=['crates/aspis-prover/src/state_only_entropy.rs','crates/aspis-r1-cost-probe/src/host_sumcheck.rs','crates/aspis-r1-cost-probe/src/host_work.rs','docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs','docs/research/v8-r0-zk-20261009/z4/z9e.rs','crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs','crates/aspis-r1-cost-probe/src/r1_wire.rs','crates/aspis-r1-cost-probe/src/host_wire.rs','crates/aspis-r1-cost-probe/src/sim.rs','crates/aspis-r1-cost-probe/src/RealR1_client.rs','tools/r1-cost-probe/src/bin/devnet_spend.rs','tools/r1-cost-probe/src/bin/devnet_spend/plan.rs']
rows=[]
for rel in paths:
 b=subprocess.check_output(['git','show','HEAD:'+rel]);p=E/'source'/rel;p.parent.mkdir(parents=True,exist_ok=True);p.with_suffix(p.suffix+'.txt').write_bytes(b);rows.append(dict(path=rel,blob=subprocess.check_output(['git','rev-parse','HEAD:'+rel],text=True).strip(),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b)))
(E/'source-pins.json').write_text(json.dumps(rows,indent=2)+'\n')
for rel in ['docs/research/v8-r0-zk-20261009/lean/R1Z/PV_Canon_Deployment.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_Canon_Prefix.lean','evidence/pv-canon-20261027/OBLIGATIONS.md']:
 b=subprocess.check_output(['git','show','HEAD:'+rel]);p=E/'prior'/(Path(rel).name+'.txt');p.parent.mkdir(exist_ok=True);p.write_bytes(b)
pkg=next(p for p in tomllib.loads((R/'Cargo.lock').read_text())['package'] if p['name']=='getrandom' and p['version']=='0.3.4')
code='''from pathlib import Path
import hashlib,json
base=Path('/home/dombarker/.cargo/registry')
p=next((base/'cache').glob('*/getrandom-0.3.4.crate'));sha=hashlib.sha256(p.read_bytes()).hexdigest();assert sha==EXPECTED
f=Path('/home/dombarker/project-offloads/codex-pv-ownd-20261029/target/release/.fingerprint/getrandom-fe336fb2b7d63711/lib-getrandom.json');j=json.loads(f.read_text());assert j['rustflags']==[]
print(json.dumps(dict(archive=str(p),sha256=sha,lock_checksum=EXPECTED,match=True,fingerprint=j)))
'''.replace('EXPECTED',repr(pkg['checksum']))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr;(E/'deployed-dependency-check.json').write_text(r.stdout)
# Script-checked source witnesses, not a complete structural source binding.
checks={
 'V225': [('crates/aspis-prover/src/state_only_entropy.rs','getrandom::fill'),('crates/aspis-prover/src/state_only_entropy.rs','[0u8; 64]')],
 'V403': [('crates/aspis-r1-cost-probe/src/host_sumcheck.rs','point[round] = transcript.semantic'),('crates/aspis-r1-cost-probe/src/host_sumcheck.rs','evaluate_state_only_polynomial(&polynomial, point[round])')],
 'V249': [('docs/research/v8-r0-zk-20261009/z4/z9e.rs','install_quiet_hook();'),('docs/research/v8-r0-zk-20261009/z4/z9e.rs','std::panic::catch_unwind'),('docs/research/v8-r0-zk-20261009/z4/z9e.rs','Instant::now()'),('docs/research/v8-r0-zk-20261009/z4/z9e.rs','QUIET.with(|q| q.set(false))')],
 'V263': [('crates/aspis-r1-cost-probe/src/host_work.rs','pool::ordered_families(pool::THREADS'),('docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs','is_worker()'),('docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs','std::panic::resume_unwind(p)')]
}
out=[]
for row,pairs in checks.items():
 for rel,needle in pairs:
  b=subprocess.check_output(['git','show','HEAD:'+rel],text=True);at=b.find(needle)
  out.append(dict(row=row,path=rel,needle=needle,line=b[:at].count('\n')+1 if at>=0 else None,found=at>=0))
(E/'source-witness-checks.json').write_text(json.dumps(out,indent=2)+'\n');assert all(x['found']for x in out),out
