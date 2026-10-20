#!/usr/bin/env python3
"""Pin exact caller guards/counter-field fission, not assume reachability."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,re,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';path='crates/aspis-r1-cost-probe/src/verifier.rs';sha=lambda b:hashlib.sha256(b).hexdigest()
git=lambda *xs:subprocess.check_output(['git','-C',str(repo),*xs])
rev=lambda s:git('rev-parse',s).decode().strip()
spec=importlib.util.spec_from_file_location('source_cut',area/'tools/public-serializer-extraction-kit/extract.py');cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
class Source:
 def __init__(self,raw):self.raw=raw
 def read_bytes(self):return self.raw
def item(raw,anchor):return cut.find_item(Source(raw),anchor)[0]
parent=rev('2aa1b879c^');candidate=rev('2aa1b879c');frozen=rev('39c2971dd');src={r:git('show',r+':'+path)for r in [parent,candidate,frozen]}
anchors={'query':'pub fn query<','query_with_geometry':'fn query_with_geometry<','tx1_finish':'fn tx1_finish<','tx1':'pub fn tx1<','tx2':'pub fn tx2<','tx2_authenticated':'pub fn tx2_authenticated<'}
fragments={}
for name,anchor in anchors.items():
 old=item(src[parent],anchor);new=item(src[candidate],anchor)
 if name!='query_with_geometry':assert old==new,(name,'caller changed at candidate7')
 fragments[name]={'parent_sha256':sha(old),'candidate_sha256':sha(new),'caller_byte_identical_at_candidate':old==new}
query=item(src[candidate],anchors['query_with_geometry']);old_query=item(src[parent],anchors['query_with_geometry'])
assert b'let i=a.next;let u=p.queries[i] as usize;let q=v.query(i);' in query
assert b'accumulate_with_node(p,a,z.mul(z).double().sub(M31::ONE),folded);' in query
assert b'} else {accumulate(p,a,u,folded);}' in query
assert query.rfind(b'accumulate(p,a,u,folded);') < query.rfind(b'mark(obs,Phase::Query(i));Ok(())')
assert b'accumulate(p,a,u,folded);mark(obs,Phase::Query(i));Ok(())' in b''.join(old_query.split())
old_acc=item(src[parent],'pub fn accumulate(');new_acc=item(src[candidate],'fn accumulate_with_node(')
marker=b'    let mut basis=';old_tail=old_acc[old_acc.index(marker):];new_tail=new_acc[new_acc.index(marker):]
assert old_tail==new_tail,'counter/payload tail changed'
assert re.findall(rb'a\.next\s*(?:\+=|-=|\*=|/=|=)',new_tail)==[b'a.next+=']
assert b'a.power=a.power.mul(p.rho);a.next+=1;' in new_tail
assert b'pub type Observer=Option<fn(Phase)>;' in src[candidate]
# Later rho source fission retains precisely the same checked counter and mark order.
frozen_query=item(src[frozen],anchors['query_with_geometry']);frozen_acc=item(src[frozen],'fn accumulate_with_node(')
assert b'a.power=a.power.mul(p.rho);a.next+=1;' in frozen_acc
assert b'accumulate_with_node(p,a,node,folded,pending);\n    mark(obs,Phase::Query(i));Ok(())' in frozen_query
expected={
'query':b'QueryGeometry::for_range(&p.queries,a.next,a.next+1)?;',
 'tx1_finish':b'QueryGeometry::for_range(&p.queries,0,k)?;',
 'tx2':b'QueryGeometry::for_range(&p.queries,a.next,22)?;',
 'tx2_authenticated':b'QueryGeometry::for_range(&p.queries,a.next,22)?;'}
for name,call in expected.items():
 body=item(src[candidate],anchors[name]);assert call in body
 if name!='query':assert b'while a.next<' in body
assert b'next:0' in item(src[candidate],'pub fn new(v:Variant)')
assert b'let a=Accumulator::new(v.variant)?;' in item(src[candidate],anchors['tx1'])
result={'candidate':candidate,'parent':parent,'frozen':frozen,'source_path':path,'source_files_sha256':{r:sha(s)for r,s in src.items()},'caller_fragments':fragments,'shared_counter_payload_tail_sha256':sha(new_tail),'single_counter_write':'a.next+=1','query_mark_after_counter':True,'observer_has_no_accumulator_borrow':True,'caller_ranges':{k:v.decode()for k,v in expected.items()},'fresh_initial_counter':0,'resume_initial_counter':'captured a.next before for_range','interpretation':'Explicit inverse-audited counter/payload field fission: work keeps reads/traces at the original index; checked increment follows work; mark(Query(old index)) follows increment. Actual source Counter theorem independently verifies successful query increments. Loop starts at its literal/captured start and internally constructs Calls witnesses. Standard source/compiler/ownership/library and sufficient-resource boundaries remain; no arbitrary index-validity or candidate-equivalence premise.'}
p=ev/'GEOMETRY-CALLER-SOURCE.json';data=json.dumps(result,indent=2)+'\n'
if a.check:assert p.read_text()==data
else:p.write_text(data)
print(json.dumps({'check':a.check,'caller_source_frames':4,'checked_counter_tail_identical':True,'source_loop_interpretation_explicit':True}))
