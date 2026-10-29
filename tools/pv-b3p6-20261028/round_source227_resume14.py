"""Lift exact private round and external-layer declarations with their attributes.
No source body or callee body is replaced by a stub. The external layers are
made opaque only at the pinned extractor boundary, with explicit ports.
"""
from pathlib import Path
import hashlib,json
p=Path('crates/aspis-statement/src/state_only_poseidon.rs');s=p.read_text();out='use aspis_core::field::{M31,CM31,QM31,P};\nuse aspis_statement::poseidon2::{POSEIDON2_WIDTH,RATE};\n'
rows=[]
names=['extension_limbs','extension_from_raw_limbs','pow5','external_linear_lazy','external_local_packed_raw','external_local_packed','external_linear_packed','full_round','full_round_m31_constants','full_round_packed','full_round_m31_constants_packed']
for name in names:
 a=s.index('fn '+name+'(');b=s.index('{',a);depth=1;i=b+1
 while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
 before=s[:a].rstrip();attr=before[before.rfind('\n')+1:]
 prefix=attr+'\n'if attr.startswith('#[')else ''
 out+=prefix+s[a:i]+'\n'
 rows.append(dict(name=name,source_begin_line=s[:a].count('\n')+1,source_end_line=s[:i].count('\n')+1,body_sha256=hashlib.sha256(s[b:i].encode()).hexdigest(),attributes=prefix.strip()))
for name in ['STATE_ONLY_POSEIDON_PACKED_LANES','EXTERNAL_LOCAL_LIMB_MODULUS_BOUND']:
 a=s.index(('pub const 'if name.startswith('STATE')else 'const ')+name);b=s.index(';',a)+1;out+=s[a:b]+'\n'
q=Path('tools/pv-b3p6-20261028/v244-missing14/original_poseidon14.rs');q.write_text(out)
Path('evidence/pv-b3p6-20261028/resume14/round-source-lifts.json').write_text(json.dumps(dict(source=str(p),source_sha256=hashlib.sha256(s.encode()).hexdigest(),lifted=str(q),lifted_sha256=hashlib.sha256(out.encode()).hexdigest(),rows=rows,purpose='Changed from whole-module copy after E0603 on unrelated private imports. Exact needed declarations and attributes only; no stub or edited function body.'),indent=2)+'\n')
