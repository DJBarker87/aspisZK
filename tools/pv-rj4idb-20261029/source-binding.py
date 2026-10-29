"""Fail-closed deployed source/control binding, with explicit semantic transports.
Not a compiler or physical-side-channel preservation proof.
"""
from pathlib import Path
import subprocess,json,hashlib,re,shlex
E=Path('evidence/pv-rj4idb-20261029');rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
read=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True)
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
# Rust lexical comparison retains literals and drops comments/whitespace only.
def toks(s):
 s=re.sub(r'//[^\n]*|/\*[\s\S]*?\*/','',s)
 return re.findall(r'"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|::|->|>=|<=|==|!=|&&|\|\||<<|>>|\+=|[^\s]',s)
p='crates/aspis-r1-cost-probe/src/prover_powers.rs';powers=read(p)
expected='''use aspis_core::field::WideExact as E;
pub fn powers<const N: usize>(x: E) -> [E; N] {
 let mut out = [E::ZERO; N]; let mut p = E::ONE; let mut i = 0usize;
 while i < N { out[i] = p; i += 1; if i < N { p = p.mul(x); } } out
}'''
assert toks(powers)==toks(expected),'every token of deployed powers must match'
prover=read('crates/aspis-r1-cost-probe/src/prover.rs');lib=read('crates/aspis-r1-cost-probe/src/lib.rs')
assert prover.count('crate::prover_powers::powers::<29>(gamma)')==1
assert '#[cfg(feature="prover")]\nmod prover_powers;' in lib
cfg=json.loads((E/'native-plan.json').read_text())['configuration']
units=cfg['units'];core=next(v for v in units if '/aspis-core-' in v['path']);cost=next(v for v in units if '/aspis-r1-cost-probe-' in v['path'])
features=json.loads(core['record']['features']);assert 'ct-host-prover' in features
assert not set(features)&{'r0-op-count','r0-e4-reference','r0-r91-audit'},features
assert 'prover' in json.loads(cost['record']['features'])
# Ordered source statement to Lean-step binding; omitted statements are rejected
# by complete token equality above, not inferred from a matching subsequence.
steps=[
 ['[E::ZERO;N]','Array.repeat N zero','copy-repeat of field-free Copy WideExact; no destructor/allocator; constant native ZERO transport'],
 ['E::ONE','ProverRwP6PowersSource.aspis_core.field.wide_exact.WideExact.ONE','literal two-quartic ONE, transported in retained dictionary'],
 ['let mut i=0usize','0#usize','initial invariant i.val+fuel=N.val'],
 ['while i<N','PowersControl.dispatch outer guard','PowersSafety.finite_total: terminating invariant; all N, including zero'],
 ['out[i]=p','Array.index_mut_usize then back p','PowersSafety.index_restore: length and bounds; full mutable restoration retained'],
 ['i+=1','Usize.wrapping_add i 1#usize','PowersSafety.increment: no wrap or overflow; release checked-add panic absent'],
 ['if i<N','PowersControl.dispatch inner guard','uses incremented i; last multiplication omitted'],
 ['p=p.mul(x)','PV_RJ4IDB_FieldWide.mul','complete CT primitive source Result law through FieldQ, FieldR, FieldQMul, FieldWide'],
 ['out','return full final array','PowersBridge.complete; final writeback and N=0 retained'],
]
field=read('crates/aspis-core/src/field.rs');wide=read('crates/aspis-core/src/field/wide_exact.rs');ct=read('crates/aspis-core/src/field/ct.rs')
# Exact local WideExact mul control, after cfg-inactive instrumentation/reference arms.
def body_at(s,needle):
 a=s.index(needle);b=s.index('{',a);i=b+1;d=1
 while d:
  d+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
wbody=body_at(wide,'pub fn mul(self, rhs: Self)')
wbody=re.sub(r'#\[cfg\(feature = "r0-op-count"\)\]\s*let _count = [^;]+;','',wbody)
a=wbody.index('#[cfg(all(feature = "r0-e4-reference"');b=wbody.index('        let ac',a);wbody=wbody[:a]+wbody[b:]
wm='''pub fn mul(self,rhs:Self)->Self {let ac=self.c0.mul(rhs.c0);let bd=self.c1.mul(rhs.c1);let cross=self.c0.add(self.c1).mul(rhs.c0.add(rhs.c1));Self{c0:ac.add(mul_u(bd)),c1:cross.sub(ac).sub(bd),}}'''
assert toks(wbody)==toks(wm),'complete cfg-selected wide mul differs'
assert toks(body_at(wide,'fn mul_u('))==toks('fn mul_u(value:QM31)->QM31{QM31{c0:super::mul_by_r(value.c1),c1:value.c0,}}')
assert '#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]' in wide
# Complete selected application primitive bodies, not just name/call inventories.
def selected_body(text,needle,last=False):
 if last:text=text[text.rindex(needle):]
 body=body_at(text,needle)
 return re.sub(r'#\[cfg\(feature = "r0-op-count"\)\]\s*let _count = [^;]+;','',body)
checks=[]
def exact(label,text,needle,expected,last=False):
 b=selected_body(text,needle,last)
 assert toks(b)==toks(expected),('complete primitive body differs',label,b)
 checks.append(dict(label=label,native_body=b,native_token_sha256=sha('\0'.join(toks(b))),complete=True))
cm=field[field.index('impl CM31 {'):];qm=field[field.index('impl QM31 {'):]
exact('CM31.add',cm,'pub fn add(self, rhs: CM31)',"pub fn add(self,rhs:CM31)->CM31{CM31{a:self.a.add(rhs.a),b:self.b.add(rhs.b),}}")
exact('CM31.sub',cm,'pub fn sub(self, rhs: CM31)',"pub fn sub(self,rhs:CM31)->CM31{CM31{a:self.a.sub(rhs.a),b:self.b.sub(rhs.b),}}")
exact('CM31.mul',cm,'pub fn mul(self, rhs: CM31)',"pub fn mul(self,rhs:CM31)->CM31{let m0=self.a.mul(rhs.a);let m1=self.b.mul(rhs.b);let m2=M31::reduce_u64((u64::from(self.a.0)+u64::from(self.b.0))*(u64::from(rhs.a.0)+u64::from(rhs.b.0)),);CM31{a:m0.sub(m1),b:m2.sub(m0).sub(m1),}}")
exact('QM31.add',qm,'pub fn add(self, rhs: QM31)',"pub fn add(self,rhs:QM31)->QM31{QM31{c0:self.c0.add(rhs.c0),c1:self.c1.add(rhs.c1),}}")
exact('QM31.sub',qm,'pub fn sub(self, rhs: QM31)',"pub fn sub(self,rhs:QM31)->QM31{QM31{c0:self.c0.sub(rhs.c0),c1:self.c1.sub(rhs.c1),}}")
exact('QM31.mul',qm,'pub fn mul(self, rhs: QM31)',"pub fn mul(self,rhs:QM31)->QM31{let m0=self.c0.mul(rhs.c0);let m1=self.c1.mul(rhs.c1);let m2=self.c0.add(self.c1).mul(rhs.c0.add(rhs.c1));QM31{c0:m0.add(mul_by_r(m1)),c1:m2.sub(m0).sub(m1),}}")
exact('mul_by_r',field,'fn mul_by_r(',"fn mul_by_r(x:CM31)->CM31{CM31{a:x.a.double().sub(x.b),b:x.a.add(x.b.double()),}}")
exact('M31.mul',field,'pub fn mul(self, rhs: M31)',"pub fn mul(self,rhs:M31)->M31{M31(reduce_u64(self.0 as u64*rhs.0 as u64))}")
exact('M31.double',field,'pub fn double(self)',"pub fn double(self)->M31{self.add(self)}")
exact('M31.reduce_u64',field,'pub fn reduce_u64(',"pub fn reduce_u64(value:u64)->M31{M31(reduce_u64(value))}")
exact('M31.add.ct',field,'pub fn add(self, rhs: Self)',"pub fn add(self,rhs:Self)->Self{Self(ct::add(self.0,rhs.0))}")
exact('M31.sub.ct',field,'pub fn sub(self, rhs: Self)',"pub fn sub(self,rhs:Self)->Self{Self(ct::sub(self.0,rhs.0))}")
exact('reduce_u64.ct',field,'fn reduce_u64(x: u64)',"fn reduce_u64(x:u64)->u32{ct::reduce64(x)}",last=True)
exact('ct.subtract_p',ct,'pub fn subtract_p(',"pub fn subtract_p(x:u32)->u32{let mask=0u32.wrapping_sub((x>=P) as u32);x.wrapping_sub(P&mask)}")
exact('ct.reduce64',ct,'pub fn reduce64(',"pub fn reduce64(x:u64)->u32{let x=(x&P as u64)+(x>>31);let x=(x&P as u64)+(x>>31);subtract_p(x as u32)}")
exact('ct.add',ct,'pub fn add(',"pub fn add(a:u32,b:u32)->u32{subtract_p(a.wrapping_add(b))}")
exact('ct.sub',ct,'pub fn sub(',"pub fn sub(a:u32,b:u32)->u32{subtract_p(a.wrapping_add(P).wrapping_sub(b))}")

primitive_rows=[
 ['WideExact::mul','PV_RJ4IDB_FieldWide.mul','PV_RJ4IDB_FieldWide.complete'],
 ['wide_exact::mul_u','PV_RJ4IDB_FieldWide.mulU','PV_RJ4IDB_FieldWide.mulU_complete'],
 ['QM31::mul','ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul','PV_RJ4IDB_FieldQMul.complete'],
 ['QM31::add','ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add','PV_RJ4IDB_FieldQ.add'],
 ['QM31::sub','PV_RJ4IDB_FieldQ.S.qsub','PV_RJ4IDB_FieldQ.sub'],
 ['mul_by_r','ProverRwP7CurrentFieldSource.aspis_core.field.mul_by_r','PV_RJ4IDB_FieldR.complete'],
 ['CM31::{add,sub,mul}','ProverRwP7CurrentFieldSource','PV_ProverRwP7CurrentComplexBridge.{add,sub,mul}'],
 ['M31::{double,add,sub,mul,reduce_u64}','ProverRwP7CurrentFieldSource','ProverRwP7CurrentBaseBridge.{double,add,sub,mul,mreduce}'],
 ['ct::{subtract_p,reduce64,add,sub}','ProverRwP7CurrentFieldSource','ProverRwP7CurrentCtBridge.{subtract_source,reduce_source,add_source,sub_source}'],
]
# Source primitives' selected bodies are bound directly; no environment/clock/
# randomness/file/network reads or mutable-global effects exist in this cone.
assert all(z not in wbody for z in ['unsafe','alloc','std::','env::','Instant','thread_local','static mut'])
source_records=[dict(path=p,sha256=sha(read(p))) for p in [p,'crates/aspis-r1-cost-probe/src/prover.rs','crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-core/src/field.rs','crates/aspis-core/src/field/ct.rs','crates/aspis-core/src/field/wide_exact.rs']]
# Read 1.94.1 standard source, without touching the host toolchain or shared trees.
code=r'''import pathlib,json,hashlib
r=pathlib.Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src');out=[]
for f,a,b in [('array/mod.rs',394,404),('slice/index.rs',24,33),('slice/index.rs',211,280),('convert/num.rs',50,130),('num/uint_macros.rs',2370,2380),('num/uint_macros.rs',2408,2418),('num/uint_macros.rs',2447,2457),('num/uint_macros.rs',2663,2676)]:
 p=r/f;s=p.read_text();text='\n'.join(s.splitlines()[a-1:b]);out.append(dict(path=str(p),file_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),start=a,end=b,text=text,sha256=hashlib.sha256(text.encode()).hexdigest()))
print(json.dumps(out))'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True);assert r.returncode==0,r.stderr
std=json.loads(r.stdout);assert 'IndexMut::index_mut(self as &mut [T], index)' in std[0]['text'];assert 'index.index_mut(self)' in std[1]['text'];assert '&mut (*slice)[self]' in std[2]['text']
result=dict(revision=rev,evidence_class='structural (K-1 substitute), source/complete-Result boundary',source_records=source_records,config_selected_core_features=features,config=cfg['profile'],static_call='prover::opening_batch -> prover_powers::powers::<29> (WideExact)',source_statement_binding=steps,primitive_binding=primitive_rows,complete_primitive_token_checks=checks,standard_source=std,standard_binding={'array_IndexMut':'unsize preserves length N and element order; forward to slice IndexMut','slice_IndexMut':'forward same index/self to SliceIndex<usize>','usize_SliceIndex':'intrinsic indexing; bound proved by PowersSafety.index_restore; unreachable panic does not execute its formatting/drop cone','From<u32> for u64':'lossless as cast; UScalar.cast source operation','usize_add':'release wrapping addition; no overflow by PowersSafety.increment','copy_drop':'WideExact, QM31, CM31, M31 are recursively Copy; no user Drop; no allocation inside powers or arithmetic; array copies/memory primitives retained at V370'},control_difference={'native':'store before multiply','result_model':'restore continuation applied in Result expression after multiply','justification':'PowersSafety.mul_total/PowersTotal.complete: selected arithmetic never fails/diverges, every final restored value preserved; this is a Result transport, not erasure of actual store/crash observations'},compiler_boundary='V370, owner D381/D386 retained; source-to-machine preservation is not asserted or added to T',effects_boundary='D348/diag, L1/L2/L3 and asynchronous crash/physical memory observation retained separately; no whole-observer law claimed',native_validation='native-powers-result.json: deployed1.94.1 opt3 exact powers source, 32768 same-input pairs incl N29; finite validation only',removed='op254 static caller source-body and primitive installation identification at the own-1 source/Result boundary',not_removed='whole native RunJoin, compiler cohort, observation, side channels, endpoint assumptions',passed=True)
(E/'op254-source-binding.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS complete powers and selected WideExact mul token bodies; source binding written')
