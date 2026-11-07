"""Prepare exact request references and frozen-body native callers."""
from pathlib import Path
import subprocess,json,re,difflib
E=Path(__file__).resolve().parent;rev='b936275465600469312d1f058cdc91ea2a11f3dc'
original=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True)
inv=json.loads((E.parent/'pool-inventory2-20261109/NKZ_INVENTORY.json').read_text())['rows']
rows=[374,375,376,377,390,391,323]
refs='''pub type Key=[u8;32];
#[derive(Clone,Copy)]
pub struct Request{pub program:Key,pub seeds:[Key;4],pub lengths:[usize;4],pub count:usize}
'''
meta={};files={};patch=''
for row in rows:
 r=next(r for r in inv if r['id']=='POOL:'+str(row));p=r['source_file'];s=original(p);a,b=r['source_lines'];body='\n'.join(s.splitlines()[a-1:b]);fn=r['function'].rsplit('::',1)[1]
 const=re.findall(r'POOL_V1_[A-Z0-9_]+_SEED',body)[0]
 decl=re.search(r'(?:pub )?const '+const+r'[^=]*=\s*b"([^"]+)"',s)
 if decl:domain=decl[1]
 else:
  # Imported statement seed constants retain their frozen owner.
  matches=[]
  for q in ['crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs','crates/aspis-statement/src/pool_v1/verifier_registry.rs']:
   z=subprocess.check_output(['git','show','4bb3b3f5:'+q],text=True);m=re.search(r'(?:pub )?const '+const+r'[^=]*=\s*b"([^"]+)"',z)
   if m:matches.append(m[1])
  assert len(matches)==1,(row,const);domain=matches[0]
 params='program:Key,pool:Key';args='program,pool';count=2;other=['pool','[0;32]','[0;32]'];lens=[len(domain),32,0,0]
 if row in [374,375]:params+=',profile:Key,release:Key';args+=',profile,release';count=4;other=['pool','profile','release'];lens=[len(domain),32,32,32]
 if row==323:
  params+=',sequence:u64';args+=',sequence';count=3;other=['pool','le_padded(sequence)','[0;32]'];lens=[len(domain),32,8,0]
 padded=list(domain.encode())+[0]*(32-len(domain));ref=f'pub fn request_{row}({params})->Request{{Request{{program,seeds:[{padded},'+','.join(other)+f'],lengths:{lens},count:{count}'+'}}\n'
 refs+=ref
 meta[str(row)]=dict(function=fn,path=p,domain=domain,constant=const,count=count,params=params,args=args,full_function_sha256=r['full_function_sha256'],frozen_body_sha256=r['frozen_body_sha256'])
 # Actual callers are added separately after this value-reference stage.
refs+='''pub fn le_padded(x:u64)->Key{let b=x.to_le_bytes();[b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7],0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]}
'''
(E/'PCG_address_reference.rs').write_text(refs)
(E/'PCG_ADDRESS_MAP.json').write_text(json.dumps(meta,indent=1)+'\n')
print('Prepared7 exact-seed references; no scope launched')
