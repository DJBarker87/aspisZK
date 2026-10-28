from pathlib import Path
import subprocess,difflib,tempfile
E=Path(__file__).resolve().parent;src='crates/aspis-r1-cost-probe/src/fast_pairing.rs'
base=subprocess.check_output(['git','show','4bb3b3f5:'+src],text=True)
with tempfile.TemporaryDirectory() as d:
 q=Path(d)/src;q.parent.mkdir(parents=True);q.write_text(base)
 for p in ['NBQ_u06_initial.patch','NBQ_u06b.patch']:subprocess.run(['git','apply','-'],cwd=d,input=(E/p).read_text(),text=True,check=True)
 old=q.read_text()
s=old.replace('use super::*;','use super::*;\n fn same4<T:PartialEq>(a:[T;4],b:[T;4])->bool {a[0]==b[0]&&a[1]==b[1]&&a[2]==b[2]&&a[3]==b[3]}')
for a,b in [('d.sums','[0;4]'),('q.limbs()','w'),('Q(w).limbs()','w'),('a.limbs()','[w[0],w[1],w[2],w[3]]'),('b.limbs()','[w[4],w[5],w[6],w[7]]'),('limbs_of(scalar)','w'),('d.c0.finish().limbs()','[0;4]'),('d.c1.finish().limbs()','[0;4]'),('a.limbs()','if CALLS==0{WANT0}else{WANT1}'),('b.limbs()','WANTK')]:
 s=s.replace(a+'=='+b,'same4('+a+','+b+')')
(E/'NBQ_u06c.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+src,tofile='b/'+src)))
