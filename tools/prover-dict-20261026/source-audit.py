"""Verify frozen production prefixes and applicability of the retained default gate."""
from pathlib import Path
import json,hashlib,subprocess
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026'
old=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/native-install/native/receipts/elf-proverw118-default/preflight.json'
x=json.loads(old.read_text());sha=lambda s:hashlib.sha256(s).hexdigest();rows=[]
changed=['crates/aspis-r1-cost-probe/src/prover.rs','crates/aspis-r1-cost-probe/src/r1_wire.rs']
for name in changed:
 base=subprocess.check_output(['git','show','da25b1e8b3:'+name],cwd=r);now=(r/name).read_bytes()
 assert now.startswith(base);tail=now[len(base):];assert tail.lstrip().startswith(b'#[cfg(kani)]')
 # Each appended top-level module is guarded; braces balanced, no original byte edited.
 text=tail.decode();depth=0;between='';count=0
 for line in text.splitlines():
  if depth==0:
   if not line.strip():continue
   if line=='#[cfg(kani)]':between='guard';continue
   assert between=='guard' and ('mod pdict_' in line),line
   between='';count+=1
  depth+=line.count('{')-line.count('}')
  assert depth>=0
 assert depth==0 and not between
 rows.append(dict(path=name,production_prefix_sha256=sha(base),raw_sha256=sha(now),appended_bytes=len(tail),guarded_modules=count))
comparisons=[]
for name,h in x['source_sha256'].items():
 p=r/name
 relevant=(name.startswith(('crates/','programs/','docs/research/v8-r0-zk-20261009/refine/','docs/research/v8-r0-zk-20261009/z4/','docs/research/v8-r0-zk-20261009/c3/','tools/r1-builder-reference/')) and (p.suffix=='.rs' or p.name in ['Cargo.toml','Cargo.lock'])) or name in ['Cargo.toml','Cargo.lock']
 if not relevant:continue
 actual=next((z['production_prefix_sha256'] for z in rows if z['path']==name),None)
 if actual is None:actual=sha(p.read_bytes()) if p.exists() else None
 comparisons.append(dict(path=name,retained_source_sha256=h,current_normal_source_sha256=actual,matches=h==actual))
out=dict(base='da25b1e8b3',native_changes=rows,normal_source_matches_retained_default=all(z['matches'] for z in comparisons),comparisons=comparisons,retained_preflight_sha256=sha(old.read_bytes()),limits='New Rust is only appended cfg(kani) harnesses. Normal cfg excludes every appended module. Later harness additions do not invalidate normal ELF or timing semantics under the existing compiler boundary; raw source pins and these exact prefixes are both retained.',trust_added=False)
(e/'source-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(dict(matches=sum(z['matches'] for z in comparisons),mismatches=[z['path'] for z in comparisons if not z['matches']]))
