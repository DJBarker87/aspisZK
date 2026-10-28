from KNG_control import *
import re
# Read-only source inventory, no compiler/prover process.
r=py(f'''from pathlib import Path
import hashlib,json
s=Path({B!r})/'KNG_src'
print(json.dumps({{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file() and p.suffix in ['.rs','.toml','.lock']}}))''');assert r.returncode==0,r.stderr
actual=json.loads(r.stdout);new=[];unchanged=[];modified=[]
for p,sha in actual.items():
 q=subprocess.run(['git','show',REV+':'+p],capture_output=True)
 if q.returncode!=0:new.append(dict(path=p,sha256=sha));continue
 expected=hashlib.sha256(q.stdout).hexdigest()
 (unchanged if expected==sha else modified).append(dict(path=p,frozen_sha256=expected,scratch_sha256=sha))
expected_parents={'crates/aspis-statement/src/lib.rs','crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-statement/src/pool_v1/pair_terminal.rs','crates/aspis-statement/src/pool_v1/pair_tree_profile.rs','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'}
assert {x['path'] for x in modified}==expected_parents,modified
# Preserve and independently check exact inclusion-only overlays.
for p in expected_parents:
 q=py(f'from pathlib import Path;print((Path({B!r})/"KNG_src"/{p!r}).read_text(),end="")');assert q.returncode==0
 before=subprocess.check_output(['git','show',REV+':'+p],text=True)
 after=q.stdout
 if p.endswith('src/lib.rs'):after=after.removeprefix('#![feature(allocator_api,next_index)]\n')
 assert after.startswith(before),p
 suffix=after[len(before):]
 assert re.fullmatch(r'(?:\s*#\[cfg\(kani\)\]\s*(?:#\[path="[\w.]+"\]\s*)?mod [\w]+;\s*)*',suffix),(p,suffix)
(E/'KNG_SOURCE_ASSOCIATION.json').write_text(json.dumps(dict(frozen_revision=REV,unchanged_files=unchanged,inclusion_only_files=modified,new_inputs=new,all_frozen_bodies_unchanged=True,overlay_check='Frozen byte prefix retained; only crate unstable-feature attributes and cfg(kani) module inclusions added. All other frozen source/manifests/lock byte-identical.'),indent=2)+'\n')
print('unchanged',len(unchanged),'inclusion only',len(modified),'new',len(new))
