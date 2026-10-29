from NEF_FNPTR_SPECIALISATION import *
import copy
src,nodes=inputs();out,tail,direct=build(src,nodes)
s=(E/'NEF_static_ref.rs.txt').read_text();cert=check_reference(s)
results=[]
for name,old,new in [('norm left','ops.add(aa,bb)','ops.add(bb,aa)'),('callback argument','ops.inv(norm)','ops.inv(bb)'),('conjugate','ops.neg(x.b)','ops.neg(x.a)'),('final inverse reuse','ops.mul(nb,inv_norm)','ops.mul(nb,norm)'),('output carrier','NEF_CM{a,b}','NEF_CM{a:b,b:a}'),('inverse tag','self.call(2,a,0)','self.call(3,a,0)')]:
 assert old in s
 try:check_reference(s.replace(old,new,1))
 except AssertionError as e:results.append(dict(name=name,rejected=True,reason=str(e)));continue
 raise AssertionError(('accepted inverse mutation',name))
# Typed specialisation changes no candidate computation or mark position.
require(out[C],src[C]+'\n#[cfg(kani)]\nmod NEF_native;\n','candidate byte identity outside harness declaration')
require(body(out[V],'mark'),[],'unit mark body')
require(body(out[P],'observer'),tok('()'),'unit constructor')
require(body(out[S],'mark'),[],'unit semantic mark body')
assert 'fn(' not in ''.join(body(out[F],'NEF_inv_static'))
(E/'NEF_SPECIALISATION_TEST_RESULTS.json').write_text(json.dumps(dict(positive=True,reference=cert,mutation_tests=results,query_tail=tail,unit_effects='empty body: no Result/state/effect operation'),indent=2)+'\n')
print(json.dumps(dict(positive=True,mutations_rejected=len(results))))
