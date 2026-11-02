"""Check inverse native-step projections and typed-fixture body identity."""
from NEK_scan import *
from NEK_recover import recover

def function(t,name):
 m=re.search(r'(?m)^(?:pub(?:\([^)]*\))?\s+)?(?:unsafe\s+)?fn '+name+r'\(',t);assert m,name
 start=m.start();brace=t.index('{',m.end());i=brace+1;d=1
 while d:d+=(t[i]=='{')-(t[i]=='}');i+=1
 return t[start:i]
def erase_unsafe(t):
 while (m:=re.search(r'\bunsafe\s*\{',t)):
  brace=t.index('{',m.start());i=brace+1;d=1
  while d:d+=(t[i]=='{')-(t[i]=='}');i+=1
  t=t[:m.start()]+t[brace+1:i-1]+t[i:]
 return t
def norm(t):return re.sub(r'\s+','',erase_unsafe(t))
out=[]
# NDN's exact additional assignment is preserved; no NDE receipt substitution.
a='NEK_K303';p='crates/aspis-statement/src/state_only_poseidon.rs';before=next(iter(recover('evidence/native-front2b-20261028/NDN_K001/receipt.json')[0].values()));after=read_json(E/(a+'_overlay.json'))[p];name='external_local_packed_raw';x=function(before,name);y=function(after,name)
z=y.replace(', ctx:&mut NDE_native::NEK_Context','');z=re.sub(r'ctx\.(NDE_\w+)',r'NDE_native::\1',z)
assert norm(x)==norm(z),(name,'NDN inverse mismatch')
out.append(dict(attempt=a,function=name,original_sha256=sha(x.encode()),instrumented_sha256=sha(y.encode()),inverse_equal_after_unsafe_access_projection=True))
# Box wrappers have precisely the frozen return/call/map_err structure.
p='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs';after=read_json(E/'NEK_K198_overlay.json')[p]
for name,child,callee in [('decode_pair_afterstate_boxed_v1','after_child','decode_pool_v1_pair_verified_afterstate_v1'),('decode_pair_live_snapshot_boxed_v1','live_child','decode_pool_v1_pair_live_snapshot_v1')]:
 x=function(frozen(p).decode(),name);y=function(after,name);z=re.sub(r'\s*ctx:&mut NEC_static_decode::NEK_Context,\n','\n',y).replace('ctx.'+child+'(bytes)',callee+'(bytes)')
 assert x==z,name
 out.append(dict(attempt='NEK_K198',function=name,frozen_sha256=sha(x.encode()),instrumented_sha256=sha(y.encode()),inverse_equal=True))
# Common's ghost observation parameter is absent from its native body.
p='programs/r1-cost-probe/src/r1_pool_adapter.rs';x=function(frozen(p).decode(),'asq8_common')
for a in ['NEK_K039','NEK_K235','NEK_K190']:
 y=function(read_json(E/(a+'_overlay.json'))[p],'asq8_common') if (E/(a+'_overlay.json')).exists() else function(read_json(E/'NEK_COMMON_FIDELITY.json.xz')[p],'asq8_common')
 z=re.sub(r'\s*record:&NDM_native::NEK_Context,\n','\n',y);assert x==z,a
 out.append(dict(attempt=a,function='asq8_common',frozen_sha256=sha(x.encode()),instrumented_sha256=sha(y.encode()),inverse_equal=True))
old=read_json(E/'NEK_COMMON_FIDELITY.json.xz');new=read_json(E/'NEK_COMMON_FIDELITY_TYPED.json.xz')
for path,names in [('programs/r1-cost-probe/src/r1_pool_adapter.rs',['asq8_common','NEK_bad_modifies']),('programs/r1-cost-probe/src/NDM_native.rs',['common_contract','NEK_real','NEK_unimplied','NEK_modifies'])]:
 for name in names:
  x=function(old[path],name);y=function(new[path],name);assert x==y,('typed generator-only repair changed target',name)
  out.append(dict(function=name,untyped_bundle_sha256=sha((E/'NEK_COMMON_FIDELITY.json.xz').read_bytes()),typed_bundle_sha256=sha((E/'NEK_COMMON_FIDELITY_TYPED.json.xz').read_bytes()),body_sha256=sha(x.encode()),body_identical=True))
(E/'NEK_NATIVE_ASSOCIATIONS.json').write_text(json.dumps(dict(check='PASS',projections=out,scope='source/native-step association with explicit verifier ghost context; preserves native contract semantic transport tool trust, not a kernel proof of Rust execution'),indent=2)+'\n');print('PASS',len(out))
