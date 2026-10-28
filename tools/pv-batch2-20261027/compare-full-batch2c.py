from pathlib import Path
import re,ast,json,hashlib
E=Path('evidence/pv-batch2-20261027/batch2c')
raw=(E/'52091-stdout.log').read_text();native=(E/'candidate/batch2c-d188-full-v2-001/receipt/stdout.log').read_text()
parts=re.findall(r'Aeneas.Std.Result.ok\s*\(true,\s*(\[.*?\])\)',raw,re.S)
assert len(parts)==3
rows=[]
for variant,s in zip(['S1','S2','D'],parts):
 a=ast.literal_eval(s);hit=re.search('PV_B2_NATIVE_FULL_OK_'+variant+r'=(\[.*\])',native);assert hit
 b=ast.literal_eval(hit[1]);assert len(a)==len(b)==1024;assert all(len(r)==8 for r in a+b);assert a==b
 rows.append(dict(variant=variant,result='ok(Ok(()),updated_array)',rows=1024,limbs=8192,all_limbs_equal=True,changes_zero_input=any(any(r) for r in a),values_sha256=hashlib.sha256(json.dumps(a,separators=(',',':')).encode()).hexdigest()))
record=dict(passed=True,scope='finite full Result/mutation fidelity witness, not universal original/copy equality',source_revision='5b11c957a0c160467a90afdf23d3d4c25228c8d0',lean_attempt=52091,native_receipt='candidate/batch2c-d188-full-v2-001/receipt/receipt.json',inputs='all-one fields and kappa, all-zero initial array; S1,S2,D',comparisons=rows,no_mutable_iterator_borrow=True,rejected_scratch_attempt='batch2c-d188-full-001: generated scratch syntax defect; retained and fixed in v2; source restored both times')
(E/'D188-FULL-COMPARISON.json').write_text(json.dumps(record,indent=2)+'\n');print('all3 complete1024×8 mutation Results match')
