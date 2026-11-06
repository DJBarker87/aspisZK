"""Check220 pattern-step and final219-return windows against frozen source."""
from pathlib import Path
import subprocess,json,difflib,hashlib,re
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
source='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'
old=subprocess.check_output(['git','show',rev+':'+source],text=True)
code=(E/'NKR_SumPattern_native.rs.txt').read_text()
def braces(s,p):
 p=s.index('{',p);q=p+1;depth=1
 while depth:depth+=(s[q]=='{')-(s[q]=='}');q+=1
 return s[p+1:q-1]
compact=lambda s:re.sub(r'\s+','',s)
p=old.index('fn finish_selector_tensor_basis(');p=old.index('while coordinate < COPY_PATTERN_LOCAL_COORDINATE_GROUPS.len()',p)
original=braces(old,p);trans=compact(original)
trans=trans.replace('pattern_selectors[output].add(scratch[COPY_SELECTOR_TENSOR_PATTERN_OFFSET+coordinate].mul(low))','NKR_pattern_op(pattern_selectors[output],NKR_pattern_op(scratch[COPY_SELECTOR_TENSOR_PATTERN_OFFSET+coordinate],low,0,l),1,l)')
actual=braces(code,code.index('fn NKR_pattern_step('));actual=actual[:actual.rfind('coordinate')]
assert trans==compact(actual),'Frozen220 pattern step differs beyond child substitutions'
parent=braces(old,old.index('fn finish_selector_tensor_basis('));tail=parent[parent.rfind('    (\n'):]
tailTrans=tail.replace('finish_pattern_basis_values(values, pattern_selectors, patterns)','NKR_finish_tail_child(values, pattern_selectors, patterns,l)')
tailActual=braces(code,code.index('fn NKR_finish_tail('))
assert compact(tailTrans)==compact(tailActual),'Frozen220 final219 tuple differs beyond child substitution'
name='crates/aspis-statement/src/pool_v1/NKR_SumPattern_native.rs'
new=old+'\n#[cfg(kani)]\n#[path="NKR_SumPattern_native.rs"]\nmod NKR_pattern_native;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source))
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name))
(E/'NKR_SumPattern_native.patch').write_text(patch)
(E/'NKR_SumPattern_TRANSCRIPTION.json').write_text(json.dumps(dict(revision=rev,source=source,original_pattern=original,translated_pattern=trans,harness_pattern=actual,original_tail=tail,translated_tail=tailTrans,harness_tail=tailActual,identity=True,source_sha256=hashlib.sha256(old.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest()),indent=2))
