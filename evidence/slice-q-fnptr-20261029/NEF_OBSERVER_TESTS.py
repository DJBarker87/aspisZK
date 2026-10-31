from NEF_OBSERVER_CERTIFICATE import *
import copy,time
src,nodes=inputs();start=time.monotonic();results=[]
def test(name,path,old,new,feat=None):
 s=src.copy();ns=copy.deepcopy(nodes)
 if path is not None:
  assert old in s[path],name;s[path]=s[path].replace(old,new,1)
 if feat:next(n for n in ns if n['name']==feat[0])['features'].append(feat[1])
 try:validate(s,ns)
 except (AssertionError,KeyError,IndexError) as e:results.append(dict(name=name,rejected=True,reason=str(e)));return
 raise AssertionError(('mutation incorrectly admitted',name))
validate(src,nodes)
test('profiling enabled',None,None,None,('aspis-r1-cost-probe-program','cu-profiling'))
test('detail phases enabled',None,None,None,('aspis-r1-cost-probe','detail-phases'))
test('eight way enabled',None,None,None,('aspis-r1-cost-probe','audit-eight-way'))
test('observer Some backend',P,'{None}','{Some(mark)}')
test('mark unconditional effect',V,'if let Some(f)=obs {f(p);}','panic!("effect"); if let Some(f)=obs {f(p);}')
test('mark branch flipped',V,'if let Some(f)=obs','if let None=obs')
test('extra injected callback call',C,'let i = a.next;','mark(Some(|_| panic!()), Phase::Parsed); let i = a.next;')
test('owned route changed',A,'r1_pool_adapter_owned.rs','r1_pool_adapter_original.rs')
test('query observer changed',C,'mark(obs, Phase::Query(i));','mark(None, Phase::Query(i));')
test('query writes observer',C,'let i = a.next;','let obs = Some(|_| panic!()); let i = a.next;')
test('query loop backend replaced',C,'a, g, obs, geometry, pending);','a, g, Some(|_| panic!()), geometry, pending);')
test('TX1 backend replaced',P,'SolanaDigest,observer()','SolanaDigest,Some(mark)')
test('owned TX2 backend replaced',O,'super::super::observer(),','Some(super::super::mark),')
test('specialisation inverse backend changed',F,'self.inv_with(M31::inv)','self.inv_with(|_| M31::ZERO)')
test('specialisation callback input changed',F,'let inv_norm = inverse(norm);','let inv_norm = inverse(self.a);')
test('specialisation callback called twice',F,'let inv_norm = inverse(norm);','let inv_norm = inverse(norm); let _ = inverse(norm);')
test('specialisation output corrupt',F,'a: self.a.mul(inv_norm),','a: self.b.mul(inv_norm),')
(E/'NEF_OBSERVER_TEST_RESULTS.json').write_text(json.dumps(dict(positive=True,mutation_tests=results,wall_seconds=time.monotonic()-start),indent=2)+'\n')
print(json.dumps(dict(positive=True,mutations_rejected=len(results))))
