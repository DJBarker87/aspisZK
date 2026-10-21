#!/usr/bin/env python3
"""Reuse prep9's modular specification on frozen (not candidate) sources."""
from pathlib import Path
import subprocess,ast,hashlib,json,sys
T=Path(__file__).resolve().parent;R=T.parents[1]
base='ce345a4bd';prefix='docs/research/100bit-spend-path-20261013/evidence/freeze-prep-20261020/prep9/'
pattern=subprocess.check_output(['git','show',base+':'+prefix+'harness/tower.py'],cwd=R,text=True)
spec=next(ast.literal_eval(n.value) for n in ast.parse(pattern).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='spec' for t in n.targets))
spec=spec.replace('prep9_spec','s7_spec')
source=R/'crates/aspis-core/src/field.rs';s=source.read_text();edits=[]
def replace(old,new,count=1,owner=None):
 global s
 assert s.count(old)>=count,old
 if owner:
  a=s.index('impl '+owner+' {'); b=s.index('\n}',a)+2
  assert old in s[a:b]
  s=s[:a]+s[a:b].replace(old,new,count)+s[b:]
 else:s=s.replace(old,new,count)
 edits.append(dict(old=old,new=new,count=count,owner=owner))
replace('#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]','#[derive(Clone, Copy, PartialEq, Eq, Debug, Default,kani::Arbitrary)]',3)
replace('fn reduce_u64(x: u64) -> u32 {','#[kani::ensures(|out:&u32| *out<P && u64::from(*out)==x % u64::from(P))]\nfn reduce_u64(x: u64) -> u32 {')
for op,formula in [('add','u64::from(self.0)+u64::from(rhs.0)'),('sub','u64::from(self.0)+u64::from(P)-u64::from(rhs.0)'),('mul','u64::from(self.0)*u64::from(rhs.0)')]:
 sig=f'pub fn {op}(self, rhs: M31) -> M31 {{'
 replace(sig,f'#[kani::requires(self.0<P && rhs.0<P)]\n#[kani::ensures(|out:&M31| out.0<P && u64::from(out.0)==({formula}) % u64::from(P))]\n'+sig)
replace('pub fn reduce_u64(value: u64) -> M31 {','#[kani::ensures(|out:&M31| out.0<P && u64::from(out.0)==value % u64::from(P))]\npub fn reduce_u64(value: u64) -> M31 {')
for ty,pref in [('CM31','c'),('QM31','q')]:
 for op,suffix in [('add','a'),('sub','s'),('mul','m')]:
  sig=f'pub fn {op}(self, rhs: {ty}) -> {ty} {{'
  replace(sig,f'#[kani::requires(s7_spec::canonical_{pref}(self) && s7_spec::canonical_{pref}(rhs))]\n#[kani::ensures(|out:&{ty}| s7_spec::canonical_{pref}(*out) && *out==s7_spec::{pref}{suffix}(self,rhs))]\n'+sig,owner=ty)
roots='\n#[cfg(kani)] mod s7_backend {use super::*;\n'
for name,target,deps,args in [('reduce','reduce_u64',[],'kani::any()'),('add','M31::add',[],'M31(kani::any()),M31(kani::any())'),('sub','M31::sub',[],'M31(kani::any()),M31(kani::any())'),('mul','M31::mul',['reduce_u64'],'M31(kani::any()),M31(kani::any())'),('reduce_public','M31::reduce_u64',['reduce_u64'],'kani::any()')]:
 roots+=f'#[kani::proof_for_contract({target})]\n'+''.join(f'#[kani::stub_verified({d})]\n' for d in deps)+f'#[kani::unwind(1)] fn backend_{name}() {{{target}({args});}}\n'
for ty,pref in [('CM31','c'),('QM31','q')]:
 for op in ['add','sub','mul']:
  deps=['M31::add','M31::sub','M31::mul','M31::reduce_u64'] if ty=='CM31' else ['CM31::'+op] if op!='mul' else ['CM31::add','CM31::sub','CM31::mul','M31::add','M31::sub']
  roots+=f'#[kani::proof_for_contract({ty}::{op})]\n'+''.join(f'#[kani::stub_verified({d})]\n' for d in deps)+f'#[kani::unwind(1)] fn backend_{pref}_{op}() {{{ty}::{op}(kani::any(),kani::any());}}\n'
roots+='}\n';s+=spec+roots
files={'src/field.rs':s,'src/field/wide_exact.rs':(R/'crates/aspis-core/src/field/wide_exact.rs').read_text()}
for rel,content in files.items():
 p=T/rel;p.parent.mkdir(exist_ok=True)
 if '--check' in sys.argv:assert p.read_text()==content,rel
 else:p.write_text(content)
meta=dict(pattern_branch=base,pattern_path=prefix+'harness/tower.py',pattern_sha256=hashlib.sha256(pattern.encode()).hexdigest(),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),edits=edits,generated={p:hashlib.sha256(s.encode()).hexdigest() for p,s in files.items()},scope='Source bodies untouched. Kani attributes, derives and independent modular specification only. Arithmetic cfg matches no-r91/no-prover S7 harness. Contract roots are eligible only when all consumed contracts have accepted receipts.')
(T/'backend-binding.json').write_text(json.dumps(meta,indent=2)+'\n')
print('Frozen backend bodies and prep9 specification bound')
