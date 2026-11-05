from pathlib import Path
import json,hashlib,subprocess,copy
E=Path(__file__).resolve().parent
x=json.loads((E/'NGM_NATIVE_INPUTS.json').read_text());n='crates/aspis-r1-cost-probe/src/verifier.rs'
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True)
def body(s,sig):
 a=s.index(sig);b=s.index('\n}',a)+2;return s[a:b]
original=body(frozen,'pub fn finish_relation(')
replacements=[('finish_relation_round(v.round0,p.alpha[0],claim,0)','round(v.round0,p.alpha[0],claim,0,log)'),('finish_relation_round(v.round1,p.alpha[1],claim,1)','round(v.round1,p.alpha[1],claim,1,log)'),('Weights::new(p.variant,&p.semantic_alpha,&p.z)','new_weights(p.variant,&p.semantic_alpha,&p.z,log)'),('weights.pair(&p.alpha[..p.variant.folds()],v.final_message,p.kappa)','pair(&weights,&p.alpha[..p.variant.folds()],v.final_message,p.kappa,log)'),('finish_query_dot(v.final_message,&a.weights)','dot(v.final_message,&a.weights,log)'),('mark(obs,Phase::Relation)','observed_mark(obs,Phase::Relation,log)'),('mark(obs,Phase::Final)','observed_mark(obs,Phase::Final,log)')]
def erase(s):
 b=body(s,'fn source_finish(').replace('fn source_finish(', 'pub fn finish_relation(').replace('obs:Observer,log:&mut Log)', 'obs:Observer)')
 for old,new in replacements:
  assert b.count(new)==1,new;b=b.replace(new,old)
 return b
actual=x['crates/aspis-r1-cost-probe/src/NGM_verifier.rs'];assert erase(actual)==original
mutations=[]
for old,new in [('a.next!=22','a.next!=21'),('actual!=a.rhs','actual==a.rhs'),('Error::Query','Error::Relation'),('return Err(Error::Relation)','return Ok(())')]:
 fission=body(actual,'fn source_finish(');changed=actual.replace(fission,fission.replace(old,new,1),1);assert changed!=actual
 try:accepted=erase(changed)==original
 except (AssertionError,ValueError):accepted=False
 assert not accepted;mutations.append(dict(change=[old,new],rejected=True))
record=dict(status='PASS source erasure only; not native/model closure',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_body_sha256=hashlib.sha256(original.encode()).hexdigest(),instrumented_body_sha256=hashlib.sha256(body(actual,'fn source_finish(').encode()).hexdigest(),replacement_sites=len(replacements),mutations=mutations)
(E/'NGM_CONTROL_ERASURE.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
