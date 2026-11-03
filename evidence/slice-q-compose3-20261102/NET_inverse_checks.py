"""Check the adopted seven-operation specialization and its precise native ANF.

This is source association, not a composed callee certificate. The native log
has arbitrary raw replies; no field arithmetic or callback value is evaluated.
"""
from pathlib import Path
import sys,json,hashlib,subprocess,copy
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(E.parent/'slice-q-fnptr-20261029'))
from NEF_OBSERVER_CERTIFICATE import tok,functions
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
def check(source):
 frozen=subprocess.check_output(['git','show',REV+':crates/aspis-core/src/field.rs'],cwd=R,text=True)
 bodies=functions(frozen)
 cm=[b for _,b in bodies['inv_with'] if 'inv_norm' in b]
 assert cm==[tok('let norm = self.a.mul(self.a).add(self.b.mul(self.b)); let inv_norm = inverse(norm); CM31 { a:self.a.mul(inv_norm), b:self.b.neg().mul(inv_norm), }')]
 wrappers=[b for _,b in bodies['inv'] if b==tok('self.inv_with(M31::inv)')];assert len(wrappers)==1
 fns=functions(source);assert len(fns['NET_fixed_backend'])==1
 code=fns['NET_fixed_backend'][0][1]
 # Both corruptions are explicit controls. Exact cfg-deleted positive body is checked.
 for text in ['#[cfg(NET_bad_argument)] let norm=M31(norm.0^1);','#[cfg(NET_bad_reply)] let a=M31(a.0^1);']:
  t=tok(text);hits=[i for i in range(len(code)-len(t)+1) if code[i:i+len(t)]==t];assert len(hits)==1
  i=hits[0];code=code[:i]+code[i+len(t):]
 expected=tok('let aa=log.call(0,x.a,x.a); let bb=log.call(0,x.b,x.b); let norm=log.call(1,aa,bb); let inv_norm=log.call(2,norm,M31(0)); let a=log.call(0,x.a,inv_norm); let nb=log.call(3,x.b,M31(0)); let b=log.call(0,nb,inv_norm); CM31{a,b}')
 assert code==expected,'changed primitive arguments/order/result'
 assert not any(t in source for t in ['static mut','UnsafeCell','RefCell','Atomic','Option<fn','stub_verified','proof_for_contract'])
 return dict(frozen_revision=REV,original_body_tokens_sha256=sha(json.dumps(cm[0])),native_anf_tokens_sha256=sha(json.dumps(code)),source_sha256=sha(source),adoption='C3-BIN ruling z(2), adopted 2026-11-02',domain='All raw native CM31 fields and seven arbitrary raw replies; arithmetic laws instantiated separately in Lean',modifies='Only local log.events/log.next; input replies and external frame unchanged',function_pointer_dependency=False,composed_credit=False,remaining=['M31::inv whole native output/call association','Supplied CLOSED M31::neg boundary bridge','Canonical and nonzero norm caller domains','Full native/emitted/cohort instantiation'])
def tests():
 s=(E/'NET_inverse.rs.txt').read_text();positive=check(s);out=[]
 for name,a,b in [('norm operand','log.call(1,aa,bb)','log.call(1,bb,bb)'),('inverse operand','log.call(2,norm,M31(0))','log.call(2,aa,M31(0))'),('real reply','CM31{a,b}','CM31{a:b,b}'),('conjugation','log.call(3,x.b,M31(0))','log.call(3,x.a,M31(0))'),('imaginary norm','log.call(0,nb,inv_norm)','log.call(0,nb,norm)'),('order','let a=log.call(0,x.a,inv_norm);\n let nb=','let nb=')]:
  assert a in s
  try:check(s.replace(a,b,1))
  except AssertionError:out.append(dict(name=name,rejected=True))
  else:raise AssertionError('mutation accepted: '+name)
 return dict(positive=positive,tests=out)
if __name__=='__main__':
 result=tests();(E/'NET_INVERSE_SOURCE.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(dict(positive=True,mutations=len(result['tests']))))
