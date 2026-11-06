"""Produce only the225 scratch module patch and exact frozen-body transcription pin."""
from pathlib import Path
import subprocess,json,difflib,hashlib,re
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
source='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'
old=subprocess.check_output(['git','show',rev+':'+source],text=True)
code=(E/'NKR_Sum_native.rs.txt').read_text()
def body(s,name):
 p=s.index('fn '+name+'(');p=s.index('{',p);q=p+1;depth=1
 while depth:depth+=(s[q]=='{')-(s[q]=='}');q+=1
 return s[p+1:q-1]
original=body(old,'qm31_sum_products_up_to4');trans=original
trans=trans.replace('left[0].mul(right[0])','NKR_sum_mul(left[0],right[0],l)')
for n in [2,3]:
 args='['+', '.join('left['+str(i)+']' for i in range(n))+'], ['+', '.join('right['+str(i)+']' for i in range(n))+']'
 trans=trans.replace('qm31_sum_products'+str(n)+'('+args+')','NKR_sum_child('+args+',l)')
trans=trans.replace('qm31_sum_products4(left, right)','NKR_sum_child(left,right,l)')
compact=lambda s:re.sub(r'\s+','',s)
assert compact(trans)==compact(body(code,'NKR_sum_dispatch')),'Frozen-body translation mismatch'
name='crates/aspis-statement/src/pool_v1/NKR_Sum_native.rs'
new=old+'\n#[cfg(kani)]\n#[path="NKR_Sum_native.rs"]\nmod NKR_sum_native;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source))
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name))
(E/'NKR_Sum_native.patch').write_text(patch)
(E/'NKR_Sum_TRANSCRIPTION.json').write_text(json.dumps(dict(revision=rev,source=source,original=original,translated=trans,harness=body(code,'NKR_sum_dispatch'),identity=True,source_sha256=hashlib.sha256(old.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest()),indent=2))
