from pathlib import Path
import subprocess,difflib,json,os,re
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
orig=lambda p:subprocess.check_output(['git','show',REV+':'+p],text=True)
def files():
 d={}
 p='programs/r1-cost-probe/src/lib.rs';s=orig(p);s=s.replace('use aspis_r1_cost_probe::verifier', '#![cfg_attr(kani, feature(allocator_api))]\n#[cfg(kani)] extern crate alloc;\nuse aspis_r1_cost_probe::verifier',1)
 s+='\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NCV_KMX;\n#[cfg(kani)] mod NCV_reference;\n'
 d[p]=s;d['programs/r1-cost-probe/src/NCV_reference.rs']=(E/'NCV_reference.rs').read_text()
 p='programs/r1-cost-probe/src/r1_pool_adapter.rs';s=orig(p)
 for name,ty,slot,size in [('master','PoolV1PairForestMasterV1',48,384),('checkpoint','PoolV1PairForestCheckpointV1',49,192),('lane','PoolV1PairForestLaneStateV1',50,768)]:
  fun='decode_lane_from_pool_release' if name=='lane' else 'decode_'+name+'_box'
  # Native equality contract on an explicitly stated rejection subdomain.
  attrs=f'''#[cfg_attr(kani, kani::requires(NCV_native::domain_{name}(bytes)))]
#[cfg_attr(kani, kani::modifies())]
#[cfg_attr(all(kani, not(ncv_negative)), kani::ensures(|r: &Result<Box<{ty}>,ProgramError>| matches!(r,Err(ProgramError::InvalidAccountData))))]
#[cfg_attr(all(kani, ncv_negative), kani::ensures(|r: &Result<Box<{ty}>,ProgramError>| !matches!(r,Err(ProgramError::InvalidAccountData))))]
'''
  s=s.replace('fn '+fun+'(',attrs+'fn '+fun+'(',1)
 s+='\n#[cfg(kani)] #[path="NCV_native.rs"] mod NCV_native;\n';d[p]=s
 d['programs/r1-cost-probe/src/NCV_native.rs']=(E/'NCV_native.rs').read_text()
 d['programs/r1-cost-probe/src/NCV_fragments.rs']=(E/'NCV_fragments.rs').read_text().replace('pub const NCV_INVERSE:bool=false;','pub const NCV_INVERSE:bool='+('true' if os.environ.get('NCV_NEGATIVE') else 'false')+';')
 d['programs/r1-cost-probe/src/NCV_box.rs']=(E/'NCV_box.rs').read_text().replace('const NCV_INVERSE:bool=false;','const NCV_INVERSE:bool='+('true' if os.environ.get('NCV_NEGATIVE') else 'false')+';')
 case=os.environ.get('NCV_CASE')
 if case:
  assert case in ['short','long','empty','version','lanes','encoding','depth']
  npath='programs/r1-cost-probe/src/NCV_native.rs';n=d[npath]
  for name,size in [('master',384),('checkpoint',192),('lane',768)]:
   length={'short':size-1,'long':size+1,'empty':0}.get(case,size)
   domain='b.len()=='+str(length)
   if case in ['version','lanes','encoding','depth']:
    idx={'version':4,'lanes':5,'encoding':6,'depth':7}[case]
    if case=='depth' and name!='lane':continue
    domain+=' && b['+str(idx)+']==0'
   n=re.sub(r'pub fn domain_'+name+r'\(b:&\[u8\]\)->bool \{[^}]+\}', 'pub fn domain_'+name+'(b:&[u8])->bool {'+domain+'}',n)
   body='let mut b:[u8;'+str(length)+']=kani::any();'
   if case in ['version','lanes','encoding','depth']:body+='b['+str(idx)+']=0;'
   body+='let _=super::'+('decode_lane_from_pool_release' if name=='lane' else 'decode_'+name+'_box')+'(&b);'
   n=re.sub(r'fn NCV_'+name+r'_contract\(\)\{[^}]+\}', 'fn NCV_'+name+'_contract(){'+body+'}',n)
  d[npath]=n
  p='programs/r1-cost-probe/src/r1_pool_adapter.rs'
  for name,ty in [('master','PoolV1PairForestMasterV1'),('checkpoint','PoolV1PairForestCheckpointV1'),('lane','PoolV1PairForestLaneStateV1')]:
   # Restore the exact reference equality in the fixed-length split.
   d[p]=d[p].replace('matches!(r,Err(ProgramError::InvalidAccountData))',f'NCV_native::matches_{name}(r,crate::NCV_reference::decode_{name}_ref(bytes))',2)
 # Inversion is an explicit matched negative property, never a rename.
 p='programs/r1-cost-probe/src/r1_pool_adapter.rs'
 if os.environ.get('NCV_NEGATIVE'):
  d[p]=re.sub(r'#\[cfg_attr\(all\(kani, not\(ncv_negative\)\), kani::ensures\([^\n]+\n','',d[p])
  d[p]=d[p].replace('cfg_attr(all(kani, ncv_negative),','cfg_attr(kani,')
 else:
  d[p]=re.sub(r'#\[cfg_attr\(all\(kani, ncv_negative\), kani::ensures\([^\n]+\n','',d[p])
  d[p]=d[p].replace('cfg_attr(all(kani, not(ncv_negative)),','cfg_attr(kani,')
 return d
if __name__=='__main__':
 d=files();out=''
 for n,s in d.items():
  try:old=orig(n)
  except subprocess.CalledProcessError:old=''
  out+=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
 (E/'NCV_harness.patch').write_text(out)
