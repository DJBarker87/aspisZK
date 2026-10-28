"""Assign candidate per-loop bounds from the retained goto loop inventory.
These are not trusted facts: the model checker must establish every unwind assertion.
"""
from pathlib import Path
import re,json,hashlib
p=Path('evidence/pv-b3p6-20261028')
text=(p/'receipts/loops133-01/receipt/stdout.log').read_text();loops={}
for m in re.finditer(r'^Loop ([^\n]+):\n  file (.*?) line (\d+)(.*?) function ([^\n]+)',text,re.M):
 name,file,line,_,fn=m.groups();line=int(line)
 if name.startswith('__rust_'):bound=2;reason='do/while(false) assertion macros'
 elif name=='memcmp.0':bound=429;reason='old214-word byte comparison; new harness compares words directly'
 elif 'endpoint_counts' in fn:bound=(3 if name.endswith('.0') else (137 if 'forest_hiding.rs' in file else 128));reason='2 endpoints per link,136 forest or127 legacy links'
 elif fn.startswith('aspis_statement::pool_v1::build_pool_v1_pair_copy_row_schedule_v1'):bound={109:8,133:22,155:4,224:21}[line];reason='literal7/21/3/20 source traversals'
 elif fn.startswith('aspis_statement::pool_v1::build_pool_v1_pair_forest_copy_row_schedule_v1'):bound={136:65,145:25}[line];reason='64 retained links then24 forest levels'
 elif 'index_range' in file:bound=3;reason='two endpoints in each flat_map array'
 elif 'into_iter.rs' in file:bound=137;reason='at most136 links'
 elif 'partition_lomuto' in fn:bound=273;reason='at most272 collected endpoints'
 elif 'quicksort::quicksort' in fn:bound=32;reason='bounded quicksort recursion/tail iterations; unwind assertions retained'
 elif 'smallsort' in fn:bound=33;reason='small-sort windows at most32'
 elif 'sift_down' in fn:bound=16;reason='heap height below16 for272 elements'
 elif 'heapsort::heapsort' in fn:bound=273;reason='at most272-element heap'
 elif 'reverse::revswap' in fn:bound=137;reason='at most136 swaps'
 elif 'kani::kani_intrinsic' in fn:bound=65;reason='usize bit width at most64'
 elif 'dedup_by' in fn:bound=273;reason='at most272 collected endpoints'
 elif 'find_existing_run' in fn:bound=273;reason='at most272 collected endpoints'
 elif 'swap_nonoverlapping_chunks' in fn:bound=3;reason='u16 swaps have fewer than8 bytes'
 else:raise RuntimeError((name,fn))
 loops[name]=dict(bound=bound,reason=reason,file=file,line=line,function=fn)
root='_RNvNtCsfVD4KMs7thn_17pv_b3p6_reference6proofs27shipped_equals_reference133.0'
loops[root]=dict(bound=215,reason='new explicit214-word equality traversal')
out=dict(default_bound=32,inventory_sha256=hashlib.sha256(text.encode()).hexdigest(),loops=loops,unwinding_assertions=True,input_restrictions_added=False,claim='candidate bounds only; no correctness credit until Kani passes')
(p/'bounds133.json').write_text(json.dumps(out,indent=2)+'\n')
print('bounded loops',len(loops))
