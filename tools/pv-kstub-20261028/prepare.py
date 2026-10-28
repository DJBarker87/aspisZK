"""Host scratch preparation. Exact KMX patch; original proof bodies retained."""
from pathlib import Path
import subprocess,shutil,re,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-kstub-20261028');S=Path('/home/dombarker/project-offloads/codex-pv-kscan-20261028');R=Path('/home/dombarker/project-offloads/codex-pv-relink-20261028')
sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha((D/'KMX_copy_stubs.patch').read_bytes())=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
subprocess.run(['git','apply',str(D/'KMX_copy_stubs.patch')],cwd=D,check=True)
attrs='\n'.join('#[kani::stub('+a+',crate::KMX_stubs::'+b+')]' for a,b in [('<[u8]>::copy_from_slice','KMX_copy_from_slice'),('core::ptr::copy_nonoverlapping','KMX_copy_nonoverlapping'),('<[u8]>::clone_from_slice','KMX_clone_from_slice'),('alloc::vec::Vec::<u8>::extend_from_slice','KMX_extend_from_slice'),('<[u8]>::to_vec','KMX_to_vec'),('alloc::alloc::realloc','KMX_realloc')])
header='#![feature(allocator_api)]\nextern crate alloc;\n#[path="'+str(D/'KMX_stubs.rs')+'"] pub mod KMX_stubs;\n'
plans=[];pins=[]
def func(s,name):
 m=re.search(r'fn '+name+r'(?:<[^\n]*>)?\(',s);assert m,name
 a=s.index('{',m.start());depth=1;i=a+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[m.start():i]
def add(pkg,name,row,index,window=None):
 p=D/pkg/'lib.rs';s=p.read_text();body=func(s,name)
 # Insert attributes before original fn, preserve complete body.
 s=s.replace(body,attrs+'\n'+body,1)
 # False postcondition after the original complete property, only on admitted execution.
 neg=body.replace('fn '+name+'(', 'fn '+name+'_negative(',1)
 j=neg.rfind('assert_eq!');assert j>=0;neg=neg[:j]+neg[j:].replace('assert_eq!','assert_ne!',1)
 s+='\n#[cfg(kani)] mod negative_'+name+' { use super::*; use std::os::unix::ffi::OsStrExt;\n#[kani::proof]\n#[kani::unwind(260)]\n'+attrs+'\n'+neg+'\n}\n'
 # negative module needs helpers in original module; instead append beside the original.
 s=s[:s.index('\n#[cfg(kani)] mod negative_'+name)]
 start=s.index(body);end=start+len(body)
 s=s[:end]+'\n#[kani::proof]\n#[kani::unwind(260)]\n'+attrs+'\n'+neg+s[end:]
 p.write_text(s)
 plans.append(dict(package=pkg,harness=name,row=row,index=index,window=window,body_sha256=sha(body.encode()),negative=name+'_negative'))
for pkg,k,names in [('cb','K07',[('path_join8','V178',124),('string_ascii8','V179',118),('string_scalar','V179',131),('push_ascii1','V182',127)]),('cblib','K01',[('join_one_byte','V178',157),('string_path','V179',160),('string_push','V182',161),('join_two','V178',164),('push_bytes','V182',165),('join_slices_two','V178',166)])]:
 dst=D/pkg;dst.mkdir();src=S/k/'package'
 for f in src.glob('*'):
  if f.is_file():shutil.copy2(f,dst/f.name);pins.append(dict(source=str(f),sha256=sha(f.read_bytes())))
 p=dst/'lib.rs';p.write_text(header+re.sub(r'#\[kani::unwind\(\d+\)\]','#[kani::unwind(260)]',p.read_text().replace('#![allow(dead_code)]','')))
 for name,row,index in names:add(pkg,name,row,index)
# Reuse the pinned candidate source snapshot, copied only to this job's private paths.
shutil.copytree(R/'native',D/'native',ignore=shutil.ignore_patterns('target'))
# Core clone uses path core/ rather than any crates/ path. Bodies remain unchanged.
p=D/'native/core/src/lib.rs';p.write_text(p.read_text().replace('#![no_std]','#![no_std]\n#![feature(allocator_api)]').replace('extern crate alloc;', 'extern crate alloc;\n#[path="'+str(D/'KMX_stubs.rs')+'"] pub mod KMX_stubs;'))
p=D/'native/core/src/field/wide_exact.rs';s=p.read_text();s+='\n'+Path(D/'arbitrary_bytes.rs').read_text();p.write_text(s)
# Add attrs to both exposed serializer roots at their original sites.
pkg='wide';dst=D/pkg;dst.mkdir();(dst/'Cargo.toml').write_text('[package]\nname="pv-kstub-wide"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[lib]\npath="lib.rs"\n[dependencies]\naspis-core={path="../native/core",features=["r0"]}\n')
s=(S/'K06/package/lib.rs').read_text();b=func(s,'wide_flat');q=func(s,'q')
ref=(S/'K06/package/reference_p6.rs').read_text();rb=func(ref,'wide_bytes_flat')
(dst/'lib.rs').write_text(header+'use aspis_core::field::{QM31,CM31,M31};\n'+q+'\n'+rb+'\n#[kani::proof]\n#[kani::unwind(260)]\n'+b.replace('super::reference_p6::wide_bytes_flat','wide_bytes_flat'))
add('wide','wide_flat','V195',152)
# all_carriers retains its private constructor access, original module body and reference.
s=p.read_text();b=func(s,'all_carriers');neg=b.replace('fn all_carriers(', 'fn all_carriers_negative(').replace('assert_eq!','assert_ne!')
s=s.replace(b,attrs+'\n'+b+'\n#[kani::proof]\n#[kani::unwind(260)]\n'+attrs+'\n'+neg);s=s.replace('#[kani::unwind(33)]','#[kani::unwind(260)]');p.write_text(s)
plans.append(dict(package='native/core',harness='all_carriers',negative='all_carriers_negative',row='V195',index=151,body_sha256=sha(b.encode()),window=None))
# Split the 129-byte gate by input-length windows; each preserves all output coordinates.
dst=D/'split';shutil.copytree('/home/dombarker/project-offloads/codex-pv-alib-20261027/block-buffer-proof',dst,ignore=shutil.ignore_patterns('target'))
p=dst/'src/lib.rs';p.write_text(p.read_text().replace('#![no_std]','#![no_std]\n#![feature(allocator_api)]').replace('pub use generic_array;', 'extern crate alloc;\n#[path="'+str(D/'KMX_stubs.rs')+'"] pub mod KMX_stubs;\npub use generic_array;'))
p=dst/'src/sealed.rs';s=p.read_text();b=func(s,'split64_coordinate');s=s.replace(b,'')
for label,condition in [('lo','n<=64'),('hi','n>64')]:
 w=b.replace('fn split64_coordinate(',f'fn split64_coordinate_{label}(').replace('kani::assume(n<=129);',f'kani::assume(n<=129);kani::assume({condition});')
 pos=s.rfind('}');s=s[:pos]+'\n#[kani::proof]\n#[kani::unwind(260)]\n'+attrs+'\n'+w+s[pos:]
 # insertion left old attributes before empty fn: remove them later
p.write_text(s.replace('    #[cfg(kani)]\n    #[kani::proof]\n    #[kani::unwind(132)]\n    \n',''))
# add handles src/sealed.rs separately using temporary lib symlink is inappropriate; explicit body insertion
s=p.read_text()
for label in ['lo','hi']:
 name='split64_coordinate_'+label;b=func(s,name);neg=b.replace('fn '+name+'(', 'fn '+name+'_negative(');j=neg.rfind('assert_eq!');neg=neg[:j]+neg[j:].replace('assert_eq!','assert_ne!',1)
 pos=s.rfind('}');s=s[:pos]+'\n#[kani::proof]\n#[kani::unwind(260)]\n'+attrs+'\n'+neg+s[pos:]
 plans.append(dict(package='split',harness=name,negative=name+'_negative',row='V233',index=117,window=label,body_sha256=sha(b.encode())))
p.write_text(s)
(D/'plans.json').write_text(json.dumps(plans,indent=2));(D/'source-pins.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(plans,indent=2))
