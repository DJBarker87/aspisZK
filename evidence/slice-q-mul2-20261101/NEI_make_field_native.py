from pathlib import Path
import json
E=Path(__file__).resolve().parent;data=json.loads((E/'NEI_FIELD_FIXTURES.json').read_text());lines=(E/'NEI_L124/stdout.log').read_text().splitlines();printed=next(json.loads(s) for s in lines if s.startswith('"{'));expected=json.loads(printed);assert len(expected)==100 and all(isinstance(x,list) for x in expected.values());(E/'NEI_FIELD_EXPECTED.json').write_text(json.dumps(expected,indent=2)+'\n')
def arr(v):return '['+','.join(str(x)+'u32' for x in v)+']'
def ctor(kind,v):
 if kind=='word':return 'M31('+str(v[0])+'u32)'
 if kind=='cm':return 'CM31{a:M31('+str(v[0])+'),b:M31('+str(v[1])+')}'
 if kind=='qm':return 'QM31{c0:'+ctor('cm',v[:2])+',c1:'+ctor('cm',v[2:4])+'}'
 return 'WideExact::from_limbs('+arr(v)+').unwrap()'
project={'word':'vec![got.0]','cm':'vec![got.a.0,got.b.0]','qm':'vec![got.c0.a.0,got.c0.b.0,got.c1.a.0,got.c1.b.0]','wide':'got.to_limbs().to_vec()'}
text='''#[cfg(test)]
mod NEI_field_fidelity {
 extern crate std;
 use self::std::{vec,vec::Vec};
 use super::{WideExact,mul_u};
 use super::super::{M31,CM31,QM31,reduce_u64,mul_by_r};
 fn check(got:Vec<u32>,mut expected:Vec<u32>){
  if std::env::var("NEI_WRONG").is_ok(){expected[0]^=1;}
  assert_eq!(got,expected);
 }
'''
for name,fn,kind,args in data['ops']:
 text+=' #[test] fn NEI_field_'+name+'(){\n'
 for i,c in enumerate(data['cases']):
  x=ctor(kind,c['x']);y=ctor(kind,c['y']);sc='M31('+str(c['scalar'])+')'
  if args=='xy':expr='('+x+').'+fn.rsplit('.',1)[-1]+'('+y+')'
  elif args=='xs':expr='('+x+').mul_m31('+sc+')'
  elif name=='m_double':expr='('+x+').double()'
  elif name in ['reduce','m_reduce']:expr=('reduce_u64' if name=='reduce' else 'M31::reduce_u64')+'('+str(c['u'])+'u64)'
  else:expr=('mul_u' if name=='mul_u' else 'mul_by_r')+'('+x+')'
  observe='vec![got]' if name=='reduce' else project[kind]
  text+=' {let got='+expr+';check('+observe+',vec!'+arr(expected[name+'/'+str(i)])+');}\n'
 text+=' }\n'
text+='}\n';(E/'NEI_field_native.rs').write_text(text)
