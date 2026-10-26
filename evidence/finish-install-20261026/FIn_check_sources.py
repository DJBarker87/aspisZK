"""Check the exact owned/shipped body and retained extraction source bindings."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2]; P=Path(__file__).resolve().parent
C=R/'lean-candidates/s9-actual-weights-new-cut-v1-20261023/attempt22-combined-constructor-v2-exact-attrs'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def span(s,start):
 a=s.index(start);b=s.index('{',a);depth=1;i=b+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
def tokens(s):return re.findall(r'\w+|[^\s\w]',s)
w=(R/'crates/aspis-r1-cost-probe/src/weights.rs').read_text()
rows={}
for name,start,file in [('new','pub fn new(variant:Variant','constructor-new.rs'),('box','fn box_from_parts(','constructor-box-from-parts.rs')]:
 a=span(w,start);b=(C/'source-snapshots'/file).read_text().strip()
 if name=='box': b=b[b.index('fn box_from_parts('):]
 assert tokens(a)==tokens(b),(name,a,b)
 rows[name]={'source_sha256':hashlib.sha256(a.encode()).hexdigest(),'retained_snapshot':str((C/'source-snapshots'/file).relative_to(R)),'token_equal':True}
for f in ['field.rs','field/wide_exact.rs','circle.rs']:
 old=C/'source-snapshots'/('wide_exact.rs' if '/' in f else f);new=R/'crates/aspis-core/src'/f
 assert digest(old)==digest(new),f
 rows[f]={'sha256':digest(new),'byte_equal':True}
v=(R/'crates/aspis-r1-cost-probe/src/verifier.rs').read_text();native=(P/'FIn_kit/src/FIn_native.rs').read_text()
for name,start,s in [('polynomial','pub fn polynomial(',v),('field','pub fn field(',w)]:
 a=span(s,start);b=span(native,start);assert a==b
 rows[name]={'source_sha256':hashlib.sha256(a.encode()).hexdigest(),'byte_equal':True}
a=span((R/'crates/aspis-core/src/state_only_prefix.rs').read_text(),'fn state_only_statement_points(')
b=span((C/'input/src/state_only_prefix.rs').read_text(),'fn state_only_statement_points(')
assert a==b
rows['statement_points']={'sha256':hashlib.sha256(a.encode()).hexdigest(),'byte_equal':True,'normalization_resolved':'CURRENT SHIPPED source already has the two explicit absorption assignments; exact match to extraction input, no pending [7,6] loop association'}
rows['normalizations']={'weights':'Namespace/import names only relative to retained normalized extraction; current shipped state_only_statement_points already matches the normalized extraction input byte-for-byte, including the two absorption assignments.','polynomial':'Generated import path only; extracted seven-step reference is separate from shipped iterator; whole arithmetic Kani001 timed out, iterator schedule Kani003 passed.'}
(P/'FIn_source-check.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Exact constructors, field files, source polynomial and field bindings PASS')
