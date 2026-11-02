"""Localize the boxed decoder's original call/reply log without deleting observations."""
from NEK_priority import *
import re

def decls(t):
 found=[]
 for match in re.finditer(r'(?:pub\s+)?static\s+mut\s+(\w+)\s*:',t):
  start=match.start();at=match.end();eq=t.index('=',at);ty=t[at:eq].strip();i=eq+1;depth=0
  while i<len(t):
   if t[i] in '[{(':depth+=1
   elif t[i] in ']})':depth-=1
   elif t[i]==';' and depth==0:break
   i+=1
  found.append((start,i+1,match[1],ty,t[eq+1:i].strip()))
 return found

def local_module(h):
 ds=decls(h);assert ds
 for start,end,*_ in reversed(ds):h=h[:start]+h[end:]
 first=re.search(r'^(?:pub\s+)?fn \w+',h,flags=re.M).start();end=h.index('#[kani::proof',first)
 header=h[:first];methods=h[first:end];harnesses=h[end:]
 names=[x[2] for x in ds]
 method_names=re.findall(r'^(?:pub\s+)?fn (\w+)\(',methods,flags=re.M)
 for name in names:
  methods=re.sub(r'\b'+name+r'\b','self.'+name,methods)
  harnesses=re.sub(r'\b'+name+r'\b','ctx.'+name,harnesses)
 for name in method_names:
  methods=re.sub(r'(?<![.\w])'+name+r'\(', 'self.'+name+'(',methods)
  # Undo the declaration itself, which becomes a receiver method next.
  methods=methods.replace('fn self.'+name+'(','fn '+name+'(')
  mut=name in ['prepare','after_child','live_child']
  methods=methods.replace('fn '+name+'(', 'fn '+name+'('+('&mut self' if mut else '&self')+',')
  methods=methods.replace('self,)','self)')
  methods=re.sub(r'^(?:pub\s+)?fn '+name+r'\(', 'pub(super) fn '+name+'(',methods,flags=re.M)
  harnesses=re.sub(r'(?<![.\w])'+name+r'\(', 'ctx.'+name+'(',harnesses)
 harnesses=re.sub(r'^#\[kani::stub\(crate::pool_v1::decode_pool_v1_pair_(?:verified_afterstate|live_snapshot)_v1,\w+\)\]\n','',harnesses,flags=re.M)
 harnesses=harnesses.replace('crate::NEC_kmx','crate::NEK_kmx')
 harnesses=re.sub(r'(fn \w+\(\)\{)',r'\1let mut ctx=NEK_Context::new();',harnesses)
 for wrapper in ['decode_pair_afterstate_boxed_v1','decode_pair_live_snapshot_boxed_v1']:
  harnesses=harnesses.replace('super::'+wrapper+'(&bytes)','super::'+wrapper+'(&mut ctx,&bytes)')
 fields=','.join('pub(super) '+name+':'+ty for _,_,name,ty,_ in ds)
 initial=','.join(name+':'+val for _,_,name,_,val in ds)
 record='pub(super) struct NEK_Context{'+fields+'}\nimpl NEK_Context{pub(super) fn new()->Self{Self{'+initial+'}}\n'+methods+'}\n'
 return header+record+harnesses,names

def make(rp):
 patch=ROOT/Path(rp).parent/'NEC_harness.patch';o=dict(patched_files(patch.read_text()));r=read_json(ROOT/rp);ni=r.get('native_command') or r['command'];selected=ni[ni.index('--harness')+1] if '--harness' in ni else r['module']
 module='NEC_static_decode' if 'NEC_static_decode' in selected else 'NEC_decode'
 m='crates/aspis-statement/src/pool_v1/'+module+'.rs';p='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs'
 if m not in o:return None,'different decoder/caller shape'
 h,names=local_module(o[m]);parent=o[p]
 # Keep only the selected native module; unused global-backed diagnostics are
 # absent. Their annotations are removed, never substituted as callee credit.
 parent='\n'.join(l for l in parent.splitlines() if not('cfg_attr(kani' in l and module+'::' not in l and 'kani::requires' not in l and 'kani::modifies()' not in l))+'\n'
 # Both boxed wrapper definitions carry the same local context type. Frozen
 # signatures/child calls reappear under the recorded inverse projection.
 for wrapper,child in [('decode_pair_afterstate_boxed_v1','after_child'),('decode_pair_live_snapshot_boxed_v1','live_child')]:
  marker='fn '+wrapper+'(\n';assert marker in parent
  parent=parent.replace(marker,marker+'    ctx:&mut '+module+'::NEK_Context,\n',1)
  if child=='after_child':parent=parent.replace('decode_pool_v1_pair_verified_afterstate_v1(bytes)\n            .map_err','ctx.after_child(bytes)\n            .map_err',1)
  else:parent=parent.replace('decode_pool_v1_pair_live_snapshot_v1(bytes)\n            .map_err','ctx.live_child(bytes)\n            .map_err',1)
  parent=parent.replace(wrapper+'(&bytes[',wrapper+'(&mut '+module+'::NEK_Context::new(),&bytes[')
 parent=re.sub(r'#\[cfg_attr\(kani,kani::modifies\(([^\n]*)\)\)\]',lambda mm:'#['+'cfg_attr(kani,kani::modifies('+mm[1].replace(module+'::','ctx.')+'))]',parent)
 for post in ['post_after','post_live','after_post','live_post']:parent=parent.replace(module+'::'+post+'(', 'ctx.'+post+'(')
 # Strip all appended harness module declarations then retain selected one only.
 at=parent.find('\n#[cfg(kani)]',parent.find('pub(crate) fn decode_pool_v1_pair_late_public_statement_boxed_v1'))
 if at>=0:parent=parent[:at]+'\n'
 parent+='\n#[cfg(kani)] #[path="'+module+'.rs"] mod '+module+';\n'
 result=kmx('crates/aspis-statement');result[p]=parent;result[m]=h
 for key,t in o.items():
  if key.endswith('.rs') and ('arbitrary.rs' in key or 'reference.rs' in key):result[key]=t
 for rootfile in ['crates/aspis-core/src/lib.rs','crates/aspis-statement/src/pool_v1/mod.rs']:
  if rootfile in o:result[rootfile]=o[rootfile]
 assert all('static mut' not in t for t in result.values())
 return result,'original boxed property, typed child outcome and full selected call/reply log in local context; context-native association and shape admission pending'

def plan():
 c=read_json(ROOT/'evidence/slice-s-leaves-20261029/NEC_CLOSED.json')[1]
 return [v for pair in zip(c['kani_receipt_paths'],c['control_receipts']) for v in pair]
def run(start=120):
 for i,rp in enumerate(plan()):
  a=f'NEK_K{start+i:03}'
  if (E/a/'receipt.json').exists():continue
  o,method=make(rp);assert o is not None,method
  v=publish(a,rp,o,i%2==1,method)
  if 'error: could not compile' in (E/a/'stdout.log').read_text():raise SystemExit('own compile fault: inspect before further launch')
  if v=='OPEN':break
if __name__=='__main__':
 if os.environ.get('NEK_PLAN_ONLY'):
  for rp in plan():
   o,method=make(rp);print(rp,len(o) if o else method)
 else:run(int(sys.argv[1]) if len(sys.argv)>1 else 120)
