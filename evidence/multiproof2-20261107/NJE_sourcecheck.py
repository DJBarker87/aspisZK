"""Frozen source-fission checks; never supplies a semantic verdict by itself."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
s=subprocess.check_output(['git','show',REV+':crates/aspis-r1-cost-probe/src/multiproof.rs'],text=True);h=(E/'NJE_harness.rs').read_text()
def body(text,name):
 m=re.search(r'fn '+re.escape(name)+r'\s*\(',text);assert m
 i=text.index('{',m.end());j=i+1;depth=1
 while depth:depth+=(text[j]=='{')-(text[j]=='}');j+=1
 return text[i+1:j-1]
def tokens(s):return re.sub(r'\s+','',s)
frozen=body(s,'well_formed');logged=body(h,'NJE_well_wrapper').replace('super::MAX_BATCH','MAX_BATCH').replace('NJE_order_all(log,indices)','indices.windows(2).all(|w| w[0] < w[1])').replace('NJE_domain_all(log,indices)','indices.iter().all(|&i| i < 1 << LEAF_BITS)')
assert tokens(frozen)==tokens(logged)
pins=dict(frozen_revision=REV,source_sha256=hashlib.sha256(s.encode()).hexdigest(),harness_sha256=hashlib.sha256(h.encode()).hexdigest(),well_wrapper_exact_token_erasure=True,substitutions=['windows(2).all ordered predicate -> SAME indices order-all boundary','iter().all range predicate -> SAME indices domain-all boundary'],native_credit=False,remaining='Native pass/control and list/default-all/iterator model cut association are required, not inferred from syntax')
(E/'NJE_SOURCE_ASSOCIATION.json').write_text(json.dumps(pins,indent=2)+'\n')
print('NJE well wrapper source fission token erasure checked; exact two SAME-slice call boundaries')

poseidon=subprocess.check_output(['git','show',REV+':crates/aspis-statement/src/poseidon2.rs'],text=True)
shifts=re.search(r'const INTERNAL_SHIFTS:.*?=\s*\[(.*?)\];',poseidon,re.S);assert shifts
values=[int(v.strip()) for v in shifts[1].split(',') if v.strip()]
assert values==[0,1,2,3,4,5,6,7,8,10,12,13,14,15,16]
pins['poseidon_sha256']=hashlib.sha256(poseidon.encode()).hexdigest();pins['INTERNAL_SHIFTS']=values
(E/'NJE_SOURCE_ASSOCIATION.json').write_text(json.dumps(pins,indent=2)+'\n')
def braced(text,start):
 i=text.index('{',start);j=i+1;depth=1
 while depth:depth+=(text[j]=='{')-(text[j]=='}');j+=1
 return text[i+1:j-1]
count=body(s,'node_count');iteration=braced(count,count.index('while i < n'))
iteration=re.sub(r'let mut j = i;\s*while j < n && index_at\(&level, j\) >> arity.bits\(\) == parent\s*\{\s*j \+= 1;\s*\}', 'let j=NJE_group(log,level,i,parent);',iteration)
iteration=iteration.replace('index_at(&level,','index_at(level,').replace('arity.bits()','Arity::Two.bits()').replace('arity.width()','Arity::Two.width()')
logged=body(h,'NJE_count_row');logged=braced(logged,logged.index('if *i<n'))
logged=logged.replace('super::','');logged=re.sub(r'\*(i|w|count)\b',r'\1',logged)
assert tokens(iteration)==tokens(logged)
pins['count_row_exact_specialized_token_erasure']=True
pins['count_row_substitutions']=['one while-body iteration -> guarded one-step function under rule B','arity -> Two, own adopted binary domain','inner grouping loop -> SAME level/i/parent logged group reply','local i/w/count -> by-reference parameters; no statement reordering']
(E/'NJE_SOURCE_ASSOCIATION.json').write_text(json.dumps(pins,indent=2)+'\n')
print('NJE count-row source fission checked: only binary specialization, inner group cut, and local-variable parameterization')
