"""Generate only original-attempt prefixes; callback outputs stay symbolic."""
from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
base=(L/'PV_RE_AttemptContext7.lean').read_text();start=base.index('  letI : ExternalFuns := D');end=base.index('  exact ⟨_,rfl⟩',start);proof=base[start:end]
common='''    (bytes : alloc.vec.Vec U8) (digest : Array U8 32#usize)
    (serialization : D.op226 pub = .ok (.Ok bytes))
    (map_error : D.op12
      prover.prove_masked_attempt.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      (.Ok bytes) () = .ok (.Ok bytes))
    (first_hash : hash (publicFrame bytes) = .ok digest)'''
ctx='''    (context : Context)
    (context_prefix : D.op115 digest secret.mask_nonce = .ok context)'''
tag='''    (tag : U8) (tag_prefix : D.op234 variant = .ok tag)'''
enc='''    (encoded : Array U8 81#usize) (encode_prefix : D.op116 context = .ok encoded)'''
frame='''def bindingFrame (bytes : alloc.vec.Vec U8) (tag : U8)
    (encoded : Array U8 81#usize) : Slice (Slice U8) :=
  Array.to_slice (Array.make 4#usize [
    Array.to_slice (Array.make 30#usize [85#u8,78#u8,80#u8,82#u8,79#u8,86#u8,69#u8,68#u8,58#u8,82#u8,
      49#u8,58#u8,80#u8,51#u8,58#u8,80#u8,82#u8,73#u8,86#u8,65#u8,84#u8,69#u8,45#u8,65#u8,
      84#u8,84#u8,69#u8,77#u8,80#u8,84#u8]),
    alloc.vec.Vec.deref bytes, Array.to_slice (Array.make 1#usize [tag]), Array.to_slice encoded])
#print axioms bindingFrame
'''
stages=[('Tag',ctx,'D.op234 variant',[]),('Encode',ctx+'\n'+tag,'D.op116 context',['tag_prefix']),('BindingHash',ctx+'\n'+tag+'\n'+enc,'hash (bindingFrame bytes tag encoded)',['tag_prefix','encode_prefix'])]
for label,params,call,extra in stages:
 name='PV_RE_Attempt'+label+'7';s='import R1Z.PV_RE_AttemptContext7\nset_option autoImplicit false\nnoncomputable section\nnamespace R1Z.'+name+'\nopen Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep PV_RE_AttemptHashPrefix6 PV_RE_AttemptContext7\nvariable [ExternalTypes]\n'
 if label=='BindingHash':s+=frame+'\n'
 s+=f'theorem attempt_to_{label.lower()} (D : ExternalFuns) (pub : Public) (compiled : Compiled)\n    (variant : transport.Variant) (hash : Hash) (secret : Secrets) (store : Store)\n'+common+'\n'+params+' :\n    ∃ next, @prover.prove_masked_attempt _ D pub compiled variant hash secret store =\n      ('+call+' >>= next) := by\n'+proof
 s+='  change ∃ next, (D.op115 digest secret.mask_nonce >>= _) = _\n  rw [context_prefix]\n'
 if 'tag_prefix' in extra:s+='  change ∃ next, (D.op234 variant >>= _) = _\n  rw [tag_prefix]\n'
 if 'encode_prefix' in extra:s+='  change ∃ next, (D.op116 context >>= _) = _\n  rw [encode_prefix]\n'
 s+='  exact ⟨_,rfl⟩\n#print axioms attempt_to_'+label.lower()+'\nend R1Z.'+name+'\n';(L/(name+'.lean')).write_text(s)
# Concrete whole-client instantiations of the checked attempt prefixes.
for label,params,call,extra in [('Context','', 'D.op115 digest secret.mask_nonce',[])] + stages:
 name='PV_RE_Client'+label+'7';attempt='PV_RE_Attempt'+label+'7'
 s=f'import R1Z.{attempt}\nimport R1Z.PV_RE_ClientAttempt7\nimport R1Z.PV_RE_PublicPrefix6\nset_option autoImplicit false\nnoncomputable section\nnamespace R1Z.{name}\nopen Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep PV_RE_AttemptHashPrefix6 PV_RE_AttemptContext7 PV_RE_PublicPrefix6\n'
 if label=='BindingHash':s+='open PV_RE_AttemptBindingHash7\n'
 s+='variable [ExternalTypes]\n'
 header=f'''theorem client_to_{label.lower()} {{C : Type}} (D : ExternalFuns)
    (entropy : RawEntropy C) (pub : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (state state1 : C) (secret : Secrets)
    (guard : D.op233 .S2 .S2 = .ok true)
    (entropy_prefix : (EntropyWrapper D entropy).call_mut state 0#usize =
      .ok (.Ok secret,state1))
'''+common+'\n'+params
 args='D pub compiled .S2 hash secret store bytes digest serialization map_error first_hash'
 if label!='Context':args+=' context context_prefix'
 if label in ['Encode','BindingHash']:args+=' tag tag_prefix'
 if label=='BindingHash':args+=' encoded encode_prefix'
 s+=header+f''' :
    ∃ next, @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state =
      ({call} >>= next) := by
  apply PV_RE_ClientAttempt7.lift_prefix D entropy pub compiled hash store state state1 secret
    guard entropy_prefix ({call})
  exact {attempt}.attempt_to_{label.lower()} {args}
#print axioms client_to_{label.lower()}
'''
 # Exact failure/divergence propagation at the same reached call, no arbitrary
 # invocation-to-failure hypothesis is introduced.
 for outcome in ['failure','divergence']:
  val='.fail e' if outcome=='failure' else '.div';tail=' (e : Error)' if outcome=='failure' else ''
  s+=header.replace(f'theorem client_to_{label.lower()}',f'theorem client_{outcome}')+tail+f'''
    (call_{outcome} : {call} = {val}) :
    @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state = {val} := by
  obtain ⟨next,hn⟩ := client_to_{label.lower()} D entropy pub compiled hash store state state1 secret
    guard entropy_prefix bytes digest serialization map_error first_hash'''
  if label!='Context':s+=' context context_prefix'
  if label in ['Encode','BindingHash']:s+=' tag tag_prefix'
  if label=='BindingHash':s+=' encoded encode_prefix'
  s+=f'\n  rw [hn,call_{outcome}]\n  rfl\n#print axioms client_{outcome}\n'
 s+='end R1Z.'+name+'\n';s=s.replace('D.op234 variant','D.op234 .S2');(L/(name+'.lean')).write_text(s)
