"""Exact small native value cuts; no whole guard or entropy refinement inferred."""
from pathlib import Path
import re,hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028'
p='crates/aspis-core/src/field/ct.rs';s=(R/p).read_text();out=[]
expected={
 'subtract_p':'let mask = 0u32.wrapping_sub((x >= P) as u32); x.wrapping_sub(P & mask)',
 'add':'subtract_p(a.wrapping_add(b))',
 'sub':'subtract_p(a.wrapping_add(P).wrapping_sub(b))'}
for name,body in expected.items():
 m=re.search(r'pub fn '+name+r'\([^)]*\) -> u32 \{([^}]+)\}',s);assert m
 assert re.sub(r'\s+','',m[1])==re.sub(r'\s+','',body),(name,m[1])
 out.append(dict(name=name,body_sha256=hashlib.sha256(m[1].encode()).hexdigest(),native=body))
p2='docs/research/v8-r0-zk-20261009/lean/PV_L2C_M31.lean';t=(R/p2).read_text()
for fragment in ['x - ((BitVec.ofNat 32 p) &&& (0 - (if p ≤ x.toNat then 1 else 0)))','def add (x y : word) : word := subtractP (x+y)','def sub (x y : word) : word := subtractP (x + BitVec.ofNat 32 p - y)']:
 assert fragment in t
record=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),native_path=p,native_sha256=hashlib.sha256(s.encode()).hexdigest(),lean_path=p2,lean_sha256=hashlib.sha256(t.encode()).hexdigest(),cuts=out,classification='structural small value cut with Lean raw-word laws; not a whole honest guard/source execution refinement',mapping=['u32 wrapping add/sub = BitVec 32 add/sub','P = 2147483647','comparison to P = toNat comparison','Boolean cast is 0 or 1','bitwise AND = BitVec AND'],complete_result_bridge=['PV_L2C_ReferenceArithmetic.m31_add','PV_L2C_ReferenceSub.m31_sub'])
(E/'native-value-binding.json').write_text(json.dumps(record,indent=2)+'\n');print('Verified three native scalar value cuts')
