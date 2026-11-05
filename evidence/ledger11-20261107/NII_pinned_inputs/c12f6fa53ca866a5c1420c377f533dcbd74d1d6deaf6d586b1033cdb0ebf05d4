from NGL_prepare import E,P,update
import json,re
I=json.loads((E/'NGL_NATIVE_INPUTS.json').read_text());h=I[P+'NGL_owned.rs']
sizes=[58295,1768,1880,384,192,768,128,256,320]
ctor='''let mut a=core::mem::ManuallyDrop::new(account());let shape:u8=kani::any();kani::assume(shape<11);match shape{'''
for i,size in enumerate(sizes):ctor+=f'{i}=>{{let v=kani::vec::exact_vec::<u8,{size}>();a.length=Ok({size});a.bytes=Ok(v);}},'
ctor+='9=>{a.length=Err(ProgramError::AccountBorrowFailed);a.bytes=Err(ProgramError::AccountBorrowFailed);},_=>{a.length=Ok(kani::any());a.bytes=Err(ProgramError::InvalidAccountData);}}'
pattern=r'fn readonly_contract\(\)\{[^\n]*\}'
h,n=re.subn(pattern,lambda m:'fn readonly_contract(){'+ctor+'let p=Pubkey::new_from_array(kani::any());let _=core::mem::ManuallyDrop::new(require_readonly_account(&a,&p));}',h);assert n==1
# Isolate the failed distinct-step packet at its separate loop-exit partition.
start=h.index('fn distinct3_contract()');end=h.index('\n',start);part=h[start:end]
needle='kani::assume(index<3&&previous<=index);'
assert needle in part
part=part.replace(needle,needle+'#[cfg(NGL_distinct_exit)] kani::assume(previous==index);');h=h[:start]+part+h[end:]
start=h.index('fn distinct_record3(');a=h.rfind('#[kani::ensures(|r|*r)]',0,start);assert a>=0
h=h[:a]+h[a:].replace('#[kani::ensures(|r|*r)]','#[kani::ensures(|r|*r != cfg!(NGL_guard_false))]',1)
update({P+'NGL_owned.rs':h},'full_caller_readonly_domain_and_distinct_exit_partition')
p=E/'NGL_run.py';s=p.read_text();needle="if os.environ.get('NGL_CAP') in ['1768','1880','384','192','768','128','256','320']:env['RUSTFLAGS']+=' --cfg NGL_cap_'+os.environ['NGL_CAP']";s=s.replace(needle,needle+"\n if os.environ.get('NGL_DISTINCT_EXIT'):env['RUSTFLAGS']+=' --cfg NGL_distinct_exit'\n if os.environ.get('NGL_GUARD_FALSE'):env['RUSTFLAGS']+=' --cfg NGL_guard_false'");p.write_text(s)
q=[]
for i,inv in [(106,False),(107,True)]:q.append(dict(attempt=f'NGL_K{i:03}',kind='kani',target='r1_pool_adapter::owned::NGL_owned::readonly_contract',expected=int(inv),env={'NGL_INVERT':'1'} if inv else {}))
ids=[63,67,87,88]+list(range(108,120));k=0
for size in sizes[1:]:
 for inv in [False,True]:
  q.append(dict(attempt=f'NGL_K{ids[k]:03}',kind='kani',target='r1_pool_adapter::NGL_adapter::key_copy'+('_wrong' if inv else ''),expected=int(inv),env={'NGL_CAP':str(size)}));k+=1
for i,inv in [(89,False),(120,True)]:
 env={'NGL_DISTINCT_EXIT':'1'}
 if inv:env['NGL_GUARD_FALSE']='1'
 q.append(dict(attempt=f'NGL_K{i:03}',kind='kani',target='r1_pool_adapter::owned::NGL_owned::distinct3_contract',expected=int(inv),env=env))
(E/'NGL_FINAL_NATIVE_QUEUE.json').write_text(json.dumps(q,indent=1)+'\n')
