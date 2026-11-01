"""Priority local-context migrations. Original selected names/properties retained."""
from NEK_replay import *
from NEK_scan import frozen,read_json
from NEK_verdict import verdict
import difflib

def root(root,mod,body):
 n=root+'/src/lib.rs'
 return {n:'#![cfg_attr(kani, feature(allocator_api))]\n'+frozen(n).decode()+'\n#[cfg(kani)] mod '+mod+' {\n'+body+'\n}\n'}
def kmx(rootname):return root(rootname,'NEK_kmx','extern crate alloc;include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));')
def publish(a,rp,o,negative=False,method='same property, original names, local context'):
 fn=E/(a+'_overlay.json');fn.write_text(json.dumps(o,indent=2)+'\n')
 patch=E/(a+'_harness.patch');diff=[]
 for n,t in o.items():
  old=frozen(n);diff.extend(difflib.unified_diff((old or b'').decode().splitlines(True),t.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
 patch.write_text(''.join(diff))
 with (E/(a+'-driver.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NEK_replay.py'),a,rp,str(patch.relative_to(ROOT))],env={**os.environ,'NEK_OVERLAY_FILE':str(fn),'NEK_KMX_REQUIRED':'1'},stdout=f,stderr=subprocess.STDOUT)
 print(a,rp,r.returncode,flush=True)
 if r.returncode:raise SystemExit('own input fault or infrastructure stop; inspect')
 q=read_json(E/a/'receipt.json');t=(E/a/'stdout.log').read_text();v=verdict(t)
 with (E/'NEK_RESULTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,original_receipt=rp,verdict=v,expected='FAIL' if negative else 'PASS',negative=negative,method=method))+'\n')
 if (negative and v=='PASS') or (not negative and v=='FAIL'):
  with (E/'NEK_FINDINGS.md').open('a') as f:f.write(f'\nImmediate finding {a}: {rp}, {v}, original name and property retained. Credit suspended pending failure-check inspection.\n')
 return v

def nde_pair(num,start):
 rp=f'evidence/native-front2-20261028/NDE_K{num:03}/receipt.json'
 s=ROOT/Path(rp).parent/'sources/NDE_src'
 p='crates/aspis-statement/src/state_only_poseidon.rs';m='crates/aspis-statement/src/NDE_poseidon.rs'
 old=(s/p).read_text();h=(s/m).read_text();ref=(s/'crates/aspis-statement/src/NDE_reference.rs').read_text()
 # Instrumentation-only globals are moved, one for one, into an explicit record.
 names=dict(TABLE='[[u64;4];4]',ROW='usize',LIMB='usize',FLAG='bool',MATRIX_REPLY='u64',MATRIX_COUNT='usize',SCAN_REPLY='(bool,usize,usize,bool)')
 globals=[]
 for line in h.splitlines():
  if 'static mut' in line:globals.append(line)
 fields=[];initial=[];mapping={}
 for line in globals:
  import re
  match=re.search(r'static mut (\w+):(.+)=(.+);',line);assert match,line
  name,ty,val=match.groups();fields.append(f'pub(super) {name}:{ty}');initial.append(f'{name}:{val}');mapping[name]='ctx.'+name
 h='\n'.join(line for line in h.splitlines() if 'static mut' not in line)+'\n'
 record='pub(super) struct NEK_Context{'+','.join(fields)+'}\nimpl NEK_Context{fn new()->Self{Self{'+','.join(initial)+'}}}\n'
 h=h.replace('#[cfg(NDE_matrix_step)]',record+'#[cfg(NDE_matrix_step)]',1)
 for name in sorted(mapping,key=len,reverse=True):
  h=re.sub(r'\b'+name+r'\b',mapping[name],h) if False else h
 # Replace only references below the context definition, never field declarations.
 at=h.index('#[cfg(NDE_matrix_step)]');head=h[:at];body=h[at:]
 for name in sorted(mapping,key=len,reverse=True):body=re.sub(r'\b'+name+r'\b',mapping[name],body)
 h=head+body
 for name in ['NDE_matrix_cell','NDE_scan_cell','NDE_packed_after']:
  h=h.replace('fn '+name+'(){','fn '+name+'(){\n let mut ctx=NEK_Context::new();')
 h=h.replace('super::external_local_packed_raw(input)','super::external_local_packed_raw(input,&mut ctx)').replace('super::external_local_packed_raw([QM31::ZERO;4])','super::external_local_packed_raw([QM31::ZERO;4],&mut ctx)').replace('crate::NDE_kmx','crate::NEK_kmx')
 signature='fn external_local_packed_raw(input: [QM31; 4]) -> [u64; 4] {'
 assert signature in old
 old=old.replace(signature,'fn external_local_packed_raw(input: [QM31; 4], ctx:&mut NDE_native::NEK_Context) -> [u64; 4] {')
 # Other callers are not selected but must typecheck; they supply private default context.
 old=old.replace('external_local_packed_raw(input)', 'external_local_packed_raw(input,&mut NDE_native::NEK_Context::new())')
 # make constructor available to parent callers.
 h=h.replace('impl NEK_Context{fn new()', 'impl NEK_Context{pub(super) fn new()')
 for name in sorted(mapping,key=len,reverse=True):old=old.replace('NDE_native::'+name,mapping[name])
 old=old.replace('crate::NDE_kmx','crate::NEK_kmx')
 o=kmx('crates/aspis-statement');o.update({p:old,m:h,'crates/aspis-statement/src/NDE_reference.rs':ref})
 core='crates/aspis-core/src/lib.rs';o[core]=frozen(core).decode()+'\n#[cfg(kani)] mod NEK_arbitrary;\n';o['crates/aspis-core/src/NEK_arbitrary.rs']=(s/'crates/aspis-core/src/NDE_arbitrary.rs').read_text()
 for negative in [False,True]:
  a=f'NEK_K{start+int(negative):03}'
  if (E/a/'receipt.json').exists():continue
  oo=dict(o)
  if negative:oo[m]=h.replace('!= cfg!(NDE_invert)','== cfg!(NDE_invert)')
  v=publish(a,rp,oo,negative,'explicit local native-step context; same matrix/scan formula and log assertions; association pending audit')
  if v=='OPEN':break

if __name__=='__main__':nde_pair(int(sys.argv[1]),int(sys.argv[2]))
