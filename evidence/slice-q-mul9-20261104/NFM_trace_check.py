"""Read-only exact frozen cut checks and mutation controls; no native credit alone."""
from pathlib import Path
import json,re,hashlib,copy
from NFM_source_checks import body,tok
E=Path(__file__).resolve().parent
F=E.parent/'slice-q-mul7-20261104/NFF_FROZEN.json'
frozen=json.loads(F.read_text())['crates/aspis-r1-cost-probe/src/fast_dots.rs']
def check(payload):
 s=payload['crates/aspis-r1-cost-probe/src/NFM_dots.rs']
 assert 'static mut' not in s and 'Option<fn' not in s
 c=body(s,'NFM_control')
 expected='''for start in (0..26).step_by(4) {
 log.starts[log.cuts]=start; log.cuts+=1;
 for term in start..core::cmp::min(start + 4, 26) {
 NFM_record(log,start,term);
 }
 }'''
 assert tok(c)==tok(expected),'control drift'
 for header in ['for start in (0..26).step_by(4) {','for term in start..core::cmp::min(start + 4, 26) {']:
  assert ''.join(tok(header)) in ''.join(tok(frozen))
 if 'fn NFM_window_term(' in s:
  restored=body(s,'NFM_window_term')
  for lane in range(8):
   site=f'NFM_window_product(log,offset,{lane}, coefficient[{lane}], scalar.0)'
   assert restored.count(site)==1,('product site',lane)
   restored=restored.replace(site,f'u64::from(coefficient[{lane}]) * u64::from(scalar.0)')
  a=frozen.index('                let scalar');b=frozen.index('\n            }',a)
  assert tok(restored)==tok(frozen[a:b]),'window body drift'
  for cut in range(7):
   w=body(s,f'window_{cut}');start=4*cut;end=min(start+4,26)
   if 'NFM_split_frame' in s:
    assert w.count('NFM_step(&q,&g,slot,term,&mut sums,&mut log);')==1,'split step drift'
    assert f'{start}<=term && term<{end}' in w,'split position drift'
    for clause in ['slot<4','lane<8','sums[j]<=3*NFM_BOUND','replies[j]<=NFM_BOUND','scalar<2147483647','assert_eq!(g[gi].to_limbs()[lane],coeff)','assert_eq!(q.as_ptr() as usize,qp)']:
     assert clause in w,('missing split domain/frame',clause)
   else:
    assert tok(f'for term in {start}..core::cmp::min({start}+4,26){{ NFM_window_term(&q,&g,slot,term,term-{start},&mut sums,&mut log); }}')==tok(w[w.index('for term'):w.index('let mut expected')])
    assert 'NFM_fold(sums,&mut limbs);' in w
 if 'fn NFM_read_or_abort(' in s:
  expected='''match M31::from_le_bytes(q[slot*120+term*4..slot*120+term*4+4].try_into().unwrap()){Some(s)=>Ok(s),None=>Err(term)}'''
  assert tok(body(s,'NFM_read_or_abort'))==tok(expected),'abort parser drift'
 return dict(control=True,window='fn NFM_window_term(' in s,abort='fn NFM_read_or_abort(' in s,sha256=hashlib.sha256(s.encode()).hexdigest())
if __name__=='__main__':
 out=[]
 for name in ['NFM_CONTROL_PAYLOAD.json','NFM_WINDOW_PAYLOAD.json','NFM_REJECT_PAYLOAD.json','NFM_WRAPPER_PAYLOAD.json','NFM_STRICT_PAYLOAD.json','NFM_SPLIT_FRAME_PAYLOAD.json','NFM_FINAL_FRAME_PAYLOAD.json']:
  p=json.loads((E/name).read_text());r=check(p);mut=[]
  for before,after in [('(0..26).step_by(4)','(0..26).step_by(5)'),('NFM_record(log,start,term)','NFM_record(log,start,term+1)'),('coefficient[0], scalar.0','coefficient[1], scalar.0')]:
   q=copy.deepcopy(p);k='crates/aspis-r1-cost-probe/src/NFM_dots.rs'
   if before not in q[k]:continue
   q[k]=q[k].replace(before,after)
   try:check(q)
   except AssertionError:mut.append(before)
   else:
    if r['window'] or not before.startswith('coefficient'):raise AssertionError('mutation admitted')
  out.append(dict(payload=name,checks=r,rejected_mutations=mut))
 (E/'NFM_TRACE_CHECK.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
