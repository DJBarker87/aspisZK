from pathlib import Path
p=Path('evidence/native-decref2-20261028/NCX_instrument.py');s=p.read_text()
s=s.replace("elif case=='length':domain='bytes.len()!='+('256' if key=='registry' else '320')", "elif case=='length':domain='bytes.len()!='+('256' if key=='registry' else '320')\n  elif case=='reject':\n   size=256 if key=='registry' else 320;mode=6 if key=='registry' else 7;res=249 if key=='registry' else 314\n   domain=f'bytes.len()!={size} || bytes[0]==0 || bytes[4]==0 || bytes[{mode}]==0 || bytes[{res}]!=0'")
needle="  n+=f'#[kani::proof_for_contract(aspis_statement::pool_v1::verifier_registry::{fun})]\\n'+attrs+f'#[kani::unwind(34)]\\nfn NCX_{key}_contract(){{let b:[u8;{sz}]=kani::any();let _={fun}(&b);}}\\n'"
replacement=needle+'''
  if case=='reject':
   mode=6 if key=='registry' else 7;res=249 if key=='registry' else 314;third=82 if key=='registry' else 69
   old=f'fn NCX_{key}_contract(){{let b:[u8;{sz}]=kani::any();let _={fun}(&b);}}'
   body=f'fn NCX_{key}_contract(){{let stage:u8=kani::any();kani::assume(stage<5);if stage==0{{let b:[u8;{size+1}]=kani::any();let _={fun}(&b);}}else{{let mut b:[u8;{size}]=kani::any();b[0]=65;b[1]=83;b[2]={third};b[3]=50;b[4]=3;b[{mode}]=1;match stage{{1=>b[0]=0,2=>b[4]=0,3=>b[{mode}]=0,_=>b[{res}]=1}};let _={fun}(&b);}}}}'
   n=n.replace(old,body)
'''
assert needle in s;s=s.replace(needle,replacement)
p.write_text(s)
