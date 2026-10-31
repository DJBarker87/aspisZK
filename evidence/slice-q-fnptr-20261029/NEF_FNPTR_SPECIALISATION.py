"""Emit reviewable scratch-only specialisation overlays; never writes shipped files."""
from NEF_OBSERVER_CERTIFICATE import *
import difflib

def build(src,nodes):
 validate(src,nodes)
 out=src.copy()
 out[V]=out[V].replace('pub type Observer=Option<fn(Phase)>;','pub type Observer=();').replace('fn mark(obs:Observer,p:Phase) { if let Some(f)=obs {f(p);} }','fn mark(_obs:Observer,_p:Phase) {}')
 old='''fn mark(obs: crate::verifier::Observer, i: u8) {
    #[cfg(feature="detail-phases")]
    if let Some(f)=obs {f(crate::verifier::Phase::SemanticPart(i));}
    #[cfg(not(feature="detail-phases"))]
    let _=(obs,i);
}'''
 assert old in out[S];out[S]=out[S].replace(old,'fn mark(_obs: crate::verifier::Observer, _i: u8) {}')
 old='''fn observer()->verifier::Observer {
    #[cfg(feature="cu-profiling")] {Some(mark)}
    #[cfg(not(feature="cu-profiling"))] {None}
}'''
 assert old in out[P];out[P]=out[P].replace(old,'fn observer()->verifier::Observer { () }')
 assert out[S].count('verify_observed(public, bytes, hash, None)')==1
 out[S]=out[S].replace('verify_observed(public, bytes, hash, None)','verify_observed(public, bytes, hash, ())')
 # Direct call specialisation only. The externally injected API remains intact.
 out[F]=out[F].replace('self.inv_with(M31::inv)','self.NEF_inv_static()')
 marker='    /// Inverse with an injected base-field inversion backend, without'
 signature='    pub fn inv_with(self, inverse: fn(M31) -> M31) -> CM31 {'
 start=out[F].index(signature);end=out[F].index('\n    }',start)+6
 direct=out[F][start:end].replace(signature,'    pub fn NEF_inv_static(self) -> CM31 {').replace('inverse(norm)','M31::inv(norm)')
 assert direct.count('M31::inv(norm)')==1
 out[F]=out[F].replace(marker,direct+'\n\n'+marker)
 # Query mark suffix is fixed and can be independently composed at its source cut.
 tail='mark(obs, Phase::Query(i));\n    Ok((a, pending))'
 assert out[C].count(tail)==1
 out[C]+='''\n#[cfg(kani)]\nmod NEF_native;\n'''
 return out,tail,direct
if __name__=='__main__':
 src,nodes=inputs();out,tail,direct=build(src,nodes)
 patch=''.join(''.join(difflib.unified_diff(src[n].splitlines(True),s.splitlines(True),fromfile='a/'+n,tofile='b/'+n)) for n,s in out.items() if s!=src[n])
 (E/'NEF_SPECIALISATION.patch').write_text(patch)
 (E/'NEF_SPECIALISATION_PAYLOAD.json').write_text(json.dumps({n:s for n,s in out.items() if s!=src[n]}))
 (E/'NEF_FNPTR_SPECIALISATION.json').write_text(json.dumps(dict(frozen_revision=REV,observer_rewrite='Option<fn(Phase)> None domain -> unit, two mark helpers -> empty',query_tail=tail,inv_static_source=direct,inv_substitution='inverse := M31::inv; one call at the same norm',specialisation_patch_sha256=hashlib.sha256(patch.encode()).hexdigest(),scope='deployed candidate verifier and CM31::inv direct edge; batch injected API excluded',adoption='PROPOSED; native semantic source transport retained; quarantine unchanged'),indent=2)+'\n')
 print('Emitted checked source specialisations, scratch patch only')

def check_reference(reference):
 # Exact ordered ANF of the already checked frozen expression tree. Symbols are
 # scalar words; all arithmetic is left as seven recorded opaque operations.
 want='''let aa=ops.mul(x.a,x.a); let bb=ops.mul(x.b,x.b); let norm=ops.add(aa,bb); let inv_norm=ops.inv(norm); let a=ops.mul(x.a,inv_norm); let nb=ops.neg(x.b); let b=ops.mul(nb,inv_norm); NEF_CM{a,b}'''
 require(body(reference,'NEF_inv_static'),tok(want),'ordered source-to-log ANF')
 for name,tag,arity in [('mul',0,2),('add',1,2),('inv',2,1),('neg',3,1)]:
  want=f'self.call({tag},a,'+('b)' if arity==2 else '0)')
  require(body(reference,name),tok(want),('operation tag identity',name))
 return dict(order=['mul(a,a)','mul(b,b)','add(reply0,reply1)','M31::inv(reply2)','mul(a,reply3)','neg(b)','mul(reply5,reply3)'],result=['reply4','reply6'],modifies='only the local NEF_Log events and next; replies retained',fn_pointer_values=False)
