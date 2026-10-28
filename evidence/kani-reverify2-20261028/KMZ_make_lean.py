"""Named symbolic window instances; handwritten generic/row bridges are inputs."""
from pathlib import Path
import json,hashlib,re,sys
E=Path(__file__).resolve().parent;check='--check' in sys.argv
names=json.loads((E/'KMZ_LEAN_MANIFEST.json').read_text())
assert len(names)==len(set(names))==57
expected={}
def emit(name,body):
 m='KMZ_'+name
 expected[m]='import KMZ_Growth\nset_option autoImplicit false\nnamespace '+m+'\nopen KMX_CopyMeaning KMY_WindowComposition\n'+body+'\n#print axioms result\nend '+m+'\n'
for name,len_,old,new,size in [('DigestA',16,16,48,32),('DigestB',48,48,96,32),('DigestC',80,96,192,32),('RootA',0,0,32,32),('RootB',32,32,64,32)]+[(f'Query{i:02}',64+4*i,64 if i==0 else 128 if i<=16 else 256,128 if i<16 else 256,4) for i in range(22)]:
 emit(name,f'''theorem result (before garbage source : Nat → Nat) (j : Nat) (bound : j<{len_}+{size}) :
 window source (loop before garbage 0 (min {old} {new})) {len_} {size} j =
 if j<{len_} then before j else source (j-{len_}) :=
 KMZ_Growth.append_after_growth before garbage source {len_} {old} {new} {size} j (by omega) (by omega) bound''')
for i in range(11):
 lo=160*i;hi=min(1736,lo+160)
 emit(f'Body{i:02}',f'''theorem result (before garbage : Nat → Nat) (j : Nat) (range : {lo}≤j ∧ j<{hi}) :
 loop before garbage 0 (min 1736 3472) j = before j :=
 KMY_VectorComposition.growth_retains before garbage 1736 3472 j (by omega) (by omega)''')
for m,s in expected.items():
 p=E/(m+'.lean')
 if check:assert p.read_text()==s,m
 else:p.write_text(s)
final='\n'.join('import '+m for m in names)+'\n'+ '\n'.join('#print axioms '+m+'.'+('append_after_growth' if m=='KMZ_Growth' else 'result') for m in names)+'\n'
if check:assert (E/'KMZ_Final.lean').read_text()==final
else:(E/'KMZ_Final.lean').write_text(final)
records=[]
for m in names:
 p=E/(m+'.lean');s=p.read_text();assert '#print axioms' in s
 assert not re.search(r'\b(sorry|admit|norm_num|decide|native_decide)\b',s),m
 records.append(dict(module=m,sha256=hashlib.sha256(s.encode()).hexdigest(),bytes=len(s.encode()),generated=m in expected))
(E/'KMZ_LEAN_PREFLIGHT.json').write_text(json.dumps(dict(modules=records,validation='57 unique focused modules;38 generated named symbolic window applications plus19 handwritten inputs; no generated recurrence evaluation; every theorem audited; failed Clone16 and joined-digest drafts consume two compiles; duplicate capacity-length audits omitted',next_consumer='KMZ_Final.lean',final_sha256=hashlib.sha256(final.encode()).hexdigest()),indent=2)+'\n')
print('PASS:57 modules;38 named symbolic instances;19 handwritten inputs; one final manifest')
