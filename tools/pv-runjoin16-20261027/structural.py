"""Historical b4e1c2ae3a projection factoring check; not a Lean refinement proof."""
from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin16-20261027'
p='crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs'
s=subprocess.check_output(['git','show','b4e1c2ae3a:'+p],text=True);a=s.index('fn records(');b=s.index('// ---------- interface for the forest compiler',a);body=s[a:b]
frozen=subprocess.check_output(['git','show','aa906c68dc:'+p],text=True)
fa=frozen.index('fn records(');fb=frozen.index('// ---------- interface for the forest compiler',fa)
expected=frozen[fa:fb]
import re
pat=r'\{ let \[M31\(w0\), M31\(w1\), M31\(w2\), M31\(w3\), M31\(w4\), M31\(w5\), M31\(w6\), M31\(w7\)\] = ([^;]+); \[w0, w1, w2, w3, w4, w5, w6, w7\] \}'
expected,count=re.subn(pat,r'raw_owned(\1)',expected)
assert count==72
pos=expected.index('{')+1
helper="\n    fn raw_owned(d: Digest) -> [u32; 8] {\n        [d[0].0, d[1].0, d[2].0, d[3].0, d[4].0, d[5].0, d[6].0, d[7].0]\n    }\n"
expected=expected[:pos]+helper+expected[pos:]
assert body==expected
assert 'pair_empty_roots(' not in body
(E/'structural-local-mapper.json').write_text(json.dumps(dict(source_revision='b4e1c2ae3a',base_revision='aa906c68dc',only_changes_from_hoist_only_body='72 identical projections factored through concrete lexical raw_owned',projection_calls=count,helper_source_sha256=hashlib.sha256(helper.encode()).hexdigest(),classification='structural source check, not extraction acceptance or kernel refinement'),indent=2)+'\n')
print('all 72 projection replacements and unchanged remaining records bytes confirmed')
