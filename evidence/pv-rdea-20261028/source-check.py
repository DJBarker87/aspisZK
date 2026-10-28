from pathlib import Path
import subprocess,json,hashlib,re
D=Path(__file__).parent
paths=['crates/aspis-prover/src/state_only_entropy.rs','tools/r1-cost-probe/src/bin/devnet_spend/plan.rs','crates/aspis-r1-cost-probe/src/RealR1_client.rs','crates/aspis-r1-cost-probe/src/prover.rs','docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean','docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullExternalFuns.lean']
checks={}
s=Path(paths[0]).read_text(); f=Path(paths[4]).read_text()
checks['rust_literal_capacity']=s.count('String::with_capacity(69)')==1
checks['emitted_literal_capacity']=f.count('alloc.string.String.with_capacity 69#usize')==1
checks['emitted_capacity_calls']=f.count('← alloc.string.String.with_capacity')==1
checks['emitted_join_calls']=f.count('std.path.Path.join ')==1
checks['rust_name_join']='let name = reservation_name(digest,String::with_capacity(69),0);\n        self.directory.join(name)' in s
checks['emitted_name_join']='let s ← alloc.string.String.with_capacity 69#usize\n  let name1 ←\n    aspis_prover.state_only_entropy.reservation_name digest s 0#usize\n  let p ← std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref self.directory\n  std.path.Path.join alloc.string.String.Insts.CoreConvertAsRefPath p name1' in f
checks['name_fixed_shape']='if i==32 {' in s and 'name.push_str(".burn")' in s and 'let digits=["0","1","2","3","4","5","6","7","8","9","a","b","c","d","e","f"]' in s
pins=[]
for p in paths:
 b=Path(p).read_bytes();pins.append(dict(path=p,sha256=hashlib.sha256(b).hexdigest(),blob=subprocess.check_output(['git','rev-parse','HEAD:'+p],text=True).strip()))
j=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),checks=checks,pins=pins,ok=all(checks.values()),scope='Exact row op26/op30 call sites in existing ProverRwFull model. Not an exhaustive machine or third-party-library call graph.')
(D/'source-check.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(dict(ok=j['ok'],checks=checks)));assert j['ok']
