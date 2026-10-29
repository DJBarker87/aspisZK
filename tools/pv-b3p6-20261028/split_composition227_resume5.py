"""Factor only fixed sixteen-cell selection in the owned composition."""
from pathlib import Path
import re,json,hashlib,subprocess
P=Path('tools/pv-b3p6-20261028/v244');D=Path('evidence/pv-b3p6-20261028');p=P/'reference_terminal.rs';s=p.read_text();old=s
for row,target in [(0,'c1'),(1,'succ_z'),(2,'xor12_z')]:
 # The owned fixed-arity constructor preserves index order; replace its exact
 # invocation, not other occurrences of the generic array helper.
 expected=f'qm31_array!(16, column, selected_claim(claims, {row}, column))'
 assert s.count(expected)==1,(row,expected)
 s=s.replace(expected,f'select_c1_227(*claims,{row})')
s+='\n#[inline(never)]\nfn select_c1_227(claims:[QM31;84],row:usize)->[QM31;16] {\n    ['+','.join(f'selected_claim(&claims,row,{i})'for i in range(16))+']\n}\n'
p.write_text(s);(D/'split-composition227-resume5.json').write_text(json.dumps(dict(old_sha256=hashlib.sha256(old.encode()).hexdigest(),new_sha256=hashlib.sha256(s.encode()).hexdigest(),selected_rows=[0,1,2],selected_columns=list(range(16)),arithmetic_order_unchanged=True,source_link_credit=False,remaining='prove fixed16 fill/value law and apply immutable copy/frame laws; re-extract and validate changed reference'),indent=2)+'\n')
freeze=json.load(open(D/'native227-parts-source-freeze.json'));name=str(p);assert name in freeze;freeze[name]=hashlib.sha256(p.read_bytes()).hexdigest();(D/'native227-composition-source-freeze.json').write_text(json.dumps(freeze,indent=2)+'\n')
