"""Constrain the long helper's remaining array and restoration binder types."""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');p=D/'ported227-pure-resume5.lean.txt';s=p.read_text();a=s.index('/-- [pv_b3p6_reference227::reference_field::qm31_sum_products3_prepared]');b=s.index('\n/-- [',a+1);old=s[a:b];new=old;edits=[]
for m in re.finditer(r'^  let (a\d*|\([^\n]*index_mut_back[^\n]*\)) (←|:=)\s*([^\n]*)',old,re.M):
 name=m[1];rhs=m[3]
 if name.startswith('('):ty='(Array Std.U64 3#usize × (Array Std.U64 3#usize → Array (Array Std.U64 3#usize) 3#usize))'
 elif rhs.startswith('Array.repeat'):ty='Array Std.U64 3#usize'
 elif rhs.startswith('Array.update'):ty='Array Std.U64 3#usize'
 elif re.match(r'Array.index_usize sums\d*\b',rhs):ty='Array Std.U64 3#usize'
 elif re.match(r'Array.index_usize pqm\d*\.components',rhs):ty='Array aspis_core.field.M31 3#usize'
 elif not rhs or rhs=='Array.index_usize':ty='Array aspis_core.field.M31 3#usize'
 else:raise AssertionError(m[0])
 before='let '+name+' ';after='let '+name+' : '+ty+' ';assert new.count(before)==1
 new=new.replace(before,after);edits.append((before,after))
assert len(edits)>100
restored=new
for before,after in reversed(edits):assert restored.count(after)==1;restored=restored.replace(after,before)
assert restored==old
q=D/'ported227-arraytypes-resume5.lean.txt';q.write_text(s[:a]+new+s[b:]);(D/'arraytypes227-resume5.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),edits=edits,annotation_erasure_equals_input=True,data_edits=False),indent=2)+'\n');print(len(edits))
