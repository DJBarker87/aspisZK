"""Complete static event inventory. Local guards never imply a caller certificate.

Pins the actual instantiated source cone, records statement IDs and conditions,
and distinguishes diagnostic-only control laws from unproved region/caller laws.
"""
from pathlib import Path
import json,lzma,hashlib,re,collections
R=Path('evidence/pv-b3p6-20261028/resume18');I=R/'imports-b3q/pv-b3q2-20261031'
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((R/'HELPER-INPUT-PINS-D559.json').read_text())
for p in pins:assert sha(Path(p['path']).read_bytes())==p['sha256']
graph=json.loads((I/'direct3-instantiated-callcone.json').read_text())
assert not graph['unresolved'] # opaque instances remain explicitly recorded
llbc=json.loads(lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes()))['translated']
funs={f['def_id']:f for f in llbc['fun_decls']if f}
# Names come from actual instances, not pretty-printed Rust-name guesses.
names={v['id']:v['name']for v in graph['instances'].values()}
rows=[]
def inspect(v,caller,path):
 if isinstance(v,list):
  for y in v:inspect(y,caller,path)
 elif isinstance(v,dict):
  if 'id'in v and 'kind'in v and 'span'in v:
   k=v['kind'];category=None;detail=None
   if isinstance(k,dict) and 'Call'in k:
    c=k['Call']['call'];target=c['func'].get('Regular',{}).get('kind',{}).get('Fun',{})
    fid=target.get('Regular');builtin=target.get('Builtin')
    if fid is not None:
     n=names.get(fid,'')
     if any(t in n for t in ['::fmt::','expect_failed','precondition_check','panic_nounwind_fmt']):category='explicit diagnostic/precondition call';detail=dict(callee_id=fid,name=n,arguments=c['args'])
    elif isinstance(builtin,dict) and 'Index'in builtin:
     category='builtin index (implicit bounds diagnostic)';detail=dict(builtin=builtin,arguments=c['args'])
   if isinstance(k,dict) and 'Abort'in k and isinstance(k['Abort'],dict) and 'Panic'in k['Abort']:
    category='direct panic';detail=k['Abort']
   if isinstance(k,dict) and 'Assert'in k:category='MIR assertion';detail=k['Assert']
   if category:
    rows.append(dict(instance=caller,statement=v['id'],span=v['span'],category=category,detail=detail,lexical_branch_path=path,status='INVENTORIED; source-event/caller certificate OPEN'))
  # Preserve small branch conditions; never duplicate entire subtrees in paths.
  for key,y in v.items():
   if key=='Switch' and isinstance(y,dict) and 'If'in y:
    cond,yes,no=y['If'];inspect(yes,caller,path+[dict(condition=cond,branch=True)]);inspect(no,caller,path+[dict(condition=cond,branch=False)])
   else:inspect(y,caller,path)
for caller,instance in graph['instances'].items():
 f=funs[instance['id']]
 if f.get('body'):inspect(f['body'],caller,[])
# Expected index and direct-panic totals cross-check independent graph inventory.
assert sum(r['category'].startswith('builtin index')for r in rows)==sum(isinstance(b['builtin'],dict)and 'Index'in b['builtin']for b in graph['builtins'])
assert sum(r['category']=='direct panic'for r in rows)==sum(isinstance(a['abort'],dict)and 'Panic'in a['abort']for a in graph['aborts'])
counts=dict(collections.Counter(r['category']for r in rows))
assert len({(r['instance'],r['statement'],r['category'])for r in rows})==len(rows)
local={186:'PV_B3P_NextFormatting569227.handler_independent',337:'PV_B3P_InclusiveFormatting569227.handler_independent',217:'PV_B3P_InclusiveFoldFormatting569227.handler_independent',207:'PV_B3P_PreconditionFormatting569227.index_range_checks',370:'PV_B3P_InitializerFormatting569227.loop_independent',192:'PV_B3P_PreconditionFormatting569227.slice_subtraction_check',237:'PV_B3P_PreconditionFormatting569227.slice_subtraction_check'}
for r in rows:
 fid=graph['instances'][r['instance']]['id']
 if fid in local:r['local_control_law']=local[fid]
# Exact new local controls' deployed versus extraction source bodies.
def item(text,needle):
 a=text.index(needle);b=text.index('{',a);depth=1;i=b+1
 while depth:
  depth+=(text[i]=='{')-(text[i]=='}');i+=1
 return text[a:i]
def tokens(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|\d+|[^\s]',re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S))
source_rows=[]
for needle in ['default fn spec_next(', 'default fn spec_try_fold']:
 old=lzma.decompress((R/'std559-source/1.94.1/iter/range.rs.xz').read_bytes()).decode();new=lzma.decompress((R/'std559-source/nightly-2026-06-01/iter/range.rs.xz').read_bytes()).decode()
 starts=[0] if 'try_fold'in needle else [0,old.index('impl<A: Step> RangeInclusiveIteratorImpl')]
 for start in starts:
  a=item(old[start:],needle);newstart=0 if start==0 else new.index('impl<A: Step> RangeInclusiveIteratorImpl');b=item(new[newstart:],needle)
  assert tokens(a)==tokens(b)
  assert 'Step::forward_checked(self.start.clone(), 1).expect("`Step` invariants not upheld")'in a
  source_rows.append(dict(needle=needle,inclusive=start!=0 or 'try_fold'in needle,deployed_body=a,extractor_body=b,deployed_sha256=sha(a.encode()),extractor_sha256=sha(b.encode()),token_identical=True,scope='default item only; specialization selection and actual caller application OPEN'))
out=dict(input_sha256=sha((I/'direct3-instantiated-callcone.json').read_bytes()),llbc_sha256=sha(lzma.decompress((I/'PV_B3Q_DirectCone3.llbc.xz').read_bytes())),static_event_counts=counts,events=rows,range_source_parity=source_rows,universal_event_certificate=False,exact_remaining='For every actual endpoint execution on its existing guarded domain, bind every inventoried event to its source state and prove its failure/formatting branch is not taken, preserving pointer, borrow-restoration, drop/unwind and world-answer semantics. Local arithmetic or Result equality alone is insufficient.',resource_boundary='rdea-2 retained: no resource-success or witness-independent world-answer assumption added',premises_removed=[],premises_added=[],premises_weakened=[])
(R/'FORMATTING-EVENTS-D569.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(counts=counts,range_bodies_compared=len(source_rows),universal_event_certificate=False)))
