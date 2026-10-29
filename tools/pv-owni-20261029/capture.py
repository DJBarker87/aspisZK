from pathlib import Path
import json,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-owni-20261029'
base='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/'
paths=['alloc/src/vec/mod.rs','alloc/src/vec/into_iter.rs','alloc/src/raw_vec/mod.rs','alloc/src/alloc.rs','core/src/ptr/mod.rs','core/src/slice/iter.rs','core/src/iter/traits/iterator.rs','core/src/iter/adapters/take_while.rs']
code='from pathlib import Path\nimport json,hashlib\nrows=[]\n'
code+='for name in '+repr(paths)+':\n p=Path('+repr(base)+')/name;b=p.read_bytes();rows.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),text=b.decode()))\n'
code+='print(json.dumps(rows))\n'
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
rows=json.loads(r.stdout)
for name in ['crates/aspis-statement/src/constraints_v4.rs','crates/aspis-core/src/field.rs','crates/aspis-core/src/field/ct.rs','crates/aspis-prover/src/state_only_candidate_prefix.rs','crates/aspis-r1-cost-probe/src/host_semantic.rs']:
 b=(R/name).read_bytes();rows.append(dict(path=name,sha256=hashlib.sha256(b).hexdigest(),text=b.decode()))
(E/'deployed-sources.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),rows=rows),indent=2)+'\n')
print(len(rows),'source files pinned; no compile')
