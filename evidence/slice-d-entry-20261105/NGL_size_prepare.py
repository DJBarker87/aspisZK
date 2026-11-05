from NGL_prepare import E,P,update
import json
I=json.loads((E/'NGL_NATIVE_INPUTS.json').read_text());h=I[P+'NGL_owned.rs']
# Independent caller allocation shapes; no old timed-out shape is repeated.
old='let n:usize=kani::any();kani::assume(n<=58295);let mut v=kani::vec::exact_vec::<u8,58295>();v.truncate(n);a.length=Ok(n);a.bytes=Ok(v);'
new='let n:usize=kani::any();kani::assume(n<=NGL_CAP);let mut v=kani::vec::exact_vec::<u8,NGL_CAP>();v.truncate(n);a.length=Ok(n);a.bytes=Ok(v);'
assert old in h;h=h.replace(old,new)
sizes=[1768,1880,384,192,768,128,256,320]
const='\n'+''.join(f'#[cfg(NGL_cap_{n})] const NGL_CAP:usize={n};\n' for n in sizes)+'#[cfg(not(any('+','.join(f'NGL_cap_{n}' for n in sizes)+')))] const NGL_CAP:usize=58295;\n'
h+=const
update({P+'NGL_owned.rs':h},'caller_allocation_capacity_cases')
p=E/'NGL_run.py';s=p.read_text();needle="if os.environ.get('NGL_FALSE_TARGET') in ['length','data','checkpoint']:env['RUSTFLAGS']+=' --cfg NGL_false_'+os.environ['NGL_FALSE_TARGET']";s=s.replace(needle,needle+"\n if os.environ.get('NGL_CAP') in ['1768','1880','384','192','768','128','256','320']:env['RUSTFLAGS']+=' --cfg NGL_cap_'+os.environ['NGL_CAP']");p.write_text(s)
q=[];i=90
for size in sizes:
 for inv in [False,True]:
  env={'NGL_CAP':str(size)}
  if inv:env['NGL_FALSE_TARGET']='data'
  q.append(dict(attempt=f'NGL_K{i:03}',kind='kani',target='r1_pool_adapter::owned::NGL_owned::data_actual_contract',expected=int(inv),env=env));i+=1
(E/'NGL_SIZE_QUEUE.json').write_text(json.dumps(q,indent=1)+'\n')
(E/'NGL_CAPACITY_CASES.json').write_text(json.dumps({'sizes':sizes+[58295],'native_generator':'arbitrary n<=capacity, exact_vec<u8,capacity> then truncate(n); includes n=capacity with all bytes arbitrary','caller_requirement':'snapshot to_vec capacity equals its admitted exact length; library/ABI transport retained, native snapshot copy/borrow/cleanup remains OPEN','rejected_credit':'No promotion from one capacity to other capacities. Exact caller capacity cases are tested independently.'},indent=1)+'\n')
