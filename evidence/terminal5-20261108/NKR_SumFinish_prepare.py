"""Check the frozen220 inner-loop window with child-only local-record substitutions."""
from pathlib import Path
import subprocess,json,difflib,hashlib,re
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
source='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'
old=subprocess.check_output(['git','show',rev+':'+source],text=True)
code=(E/'NKR_SumFinish_native.rs.txt').read_text()
def braces(s,p):
 p=s.index('{',p);q=p+1;depth=1
 while depth:depth+=(s[q]=='{')-(s[q]=='}');q+=1
 return s[p+1:q-1]
p=old.index('fn finish_selector_tensor_basis(');p=old.index('while coordinate < end {',p)
original=braces(old,p);trans=original
trans=trans.replace('copy_tag_coordinate_value(scratch, coordinate + index, selectors)','NKR_finish_tag(scratch, coordinate + index, selectors,l)')
trans=trans.replace('values[group].add(qm31_sum_products_up_to4(tag_values, lows, count))','NKR_finish_add(values[group],NKR_finish_sum(tag_values, lows, count,l),l)')
trans=trans.replace('weights[group].add(qm31_sum_products_up_to4(weight_values, lows, count))','NKR_finish_add(weights[group],NKR_finish_sum(weight_values, lows, count,l),l)')
actual=braces(code,code.index('fn NKR_finish_batch('))
actual=actual[actual.index('let count ='):actual.index('(values,weights,coordinate)')]
compact=lambda s:re.sub(r'\s+','',s)
assert compact(trans)==compact(actual),'Frozen220 single-iteration source transcription mismatch'
name='crates/aspis-statement/src/pool_v1/NKR_SumFinish_native.rs'
new=old+'\n#[cfg(kani)]\n#[path="NKR_SumFinish_native.rs"]\nmod NKR_finish_native;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source))
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name))
(E/'NKR_SumFinish_native.patch').write_text(patch)
(E/'NKR_SumFinish_TRANSCRIPTION.json').write_text(json.dumps(dict(revision=rev,source=source,original=original,translated=trans,harness=actual,identity=True,source_sha256=hashlib.sha256(old.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest()),indent=2))
