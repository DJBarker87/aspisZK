from pathlib import Path
import sys,importlib.util,json,re,difflib,subprocess,hashlib
E=Path(__file__).resolve().parent;old=E.parent/'native-tx2f-20261027';sys.argv=['prepare','none']
s=importlib.util.spec_from_file_location('NBU_native',E/'NBU_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
attrs='\n'.join('#[kani::stub('+f+',crate::KMX_stubs::'+g+')]' for f,g in [('<[u8]>::copy_from_slice','KMX_copy_from_slice'),('core::ptr::copy_nonoverlapping','KMX_copy_nonoverlapping'),('<[u8]>::clone_from_slice','KMX_clone_from_slice'),('alloc::vec::Vec::<u8>::extend_from_slice','KMX_extend_from_slice'),('<[u8]>::to_vec','KMX_to_vec'),('alloc::alloc::realloc','KMX_realloc')])
files={}
for n in ['more','decode','codecs']:
 s=(old/f'NBN_{n}.rs.txt').read_text().replace('NBN','NBU')
 s=s.replace('#[kani::proof]','#[kani::proof]\n'+attrs)
 # Matching controls preserve input domain/call and invert the first checked equality.
 pattern=re.compile(r'(#\[kani::proof\][\s\S]*?\nfn (NBU_\w+)\(\)\{?[\s\S]*?)(?=\n#\[kani::proof\]|\Z)')
 # locate each standalone harness by brace matching to avoid swallowing following helpers
 controls=[]
 for mt in re.finditer(r'fn (NBU_\w+)\(\)\s*\{',s):
  pos=mt.start(); attr=s.rfind('#[kani::proof]',0,pos)
  if attr<0 or 'fn ' in s[attr:pos]:continue
  start=s.index('{',pos);depth=1;j=start+1
  while depth:
   depth += (s[j]=='{')-(s[j]=='}');j+=1
  block=s[attr:j]
  if 'assert_eq!' not in block:continue
  neg=block.replace(mt.group(1)+'()',mt.group(1)+'_negative()',1).replace('assert_eq!','assert_ne!',1)
  controls.append(neg)
 s+='\n'+'\n'.join(controls)+'\n'
 files[f'crates/aspis-statement/src/pool_v1/NBU_{n}.rs']=s
 (E/f'NBU_{n}.rs.txt').write_text(s)
# cfg-only scratch inclusions, exact release bodies untouched
for name,mod in [('pair_terminal','codecs'),('pair_forest_terminal','more')]:
 path=f'crates/aspis-statement/src/pool_v1/{name}.rs'
 base=subprocess.check_output(['git','show',m.REV+':'+path],text=True)
 files[path]=base+f'\n#[cfg(kani)]\n#[path="NBU_{mod}.rs"]\nmod NBU_{mod};\n'
 if name=='pair_terminal':files[path]+='\n#[cfg(kani)]\n#[path="NBU_decode.rs"]\nmod NBU_decode;\n'
m.admit('NBU_UPLOAD')
r=m.py(f'''from pathlib import Path
import json
b=Path({m.B!r})/'NBU_src'
for n,s in {files!r}.items():(b/n).write_text(s)
print('uploaded')
''');assert r.returncode==0,r.stdout+r.stderr
patch=''
for p,txt in files.items():
 if Path(p).exists():base=subprocess.check_output(['git','show',m.REV+':'+p],text=True);src='a/'+p
 else:base='';src='/dev/null'
 patch+=''.join(difflib.unified_diff(base.splitlines(True),txt.splitlines(True),fromfile=src,tofile='b/'+p))
(E/'NBU_harness.patch').write_text(patch)
