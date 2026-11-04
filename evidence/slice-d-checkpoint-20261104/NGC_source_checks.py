"""Source-erasure association for local-record call windows, with mutation tests."""
from pathlib import Path
import subprocess,json,re,hashlib
E=Path(__file__).resolve().parent
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def frozen(n):return subprocess.check_output(['git','show',F+':'+n],text=True)
def body(s,signature):
 pos=s.index(signature);start=s.index('{',pos);depth=1;i=start+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[start+1:i-1]
def normal(s):return re.sub(r'\s+','',s)
x=json.loads((E/'NGC_NATIVE_INPUTS.json').read_text());v=x['crates/aspis-r1-cost-probe/src/NGC_windows.rs'];d=x['programs/r1-cost-probe/src/NGC_digest.rs']
def check(v,d):
 heap=body(frozen('crates/aspis-core/src/r0/heap.rs'),'pub fn filled')
 want=heap.replace('out.try_reserve_exact(n)','reserve(&mut out,n,log)').replace('Error::Allocation','aspis_core::r0::Error::Allocation').replace('out.resize(n, value)','resize(&mut out,n,value,log,reply)')
 assert normal(body(v,'fn filled_window'))==normal(want),'heap instruction sequence'
 source=frozen('crates/aspis-r1-cost-probe/src/verifier.rs');new=body(source[source.index('impl Accumulator'):],'pub fn new')
 want=new.replace('Self{','Accumulator{').replace('aspis_core::r0::heap::filled(v.final_len(),K::ZERO)','filled_child(v.final_len(),K::ZERO,log,reply)')
 assert normal(body(v,'fn new_window'))==normal(want),'constructor instruction sequence'
 source=frozen('programs/r1-cost-probe/src/lib.rs');digest=body(source,'fn digest(')
 assert normal(body(d,'fn digest_window'))==normal(digest.replace('hashv(parts)','hashv_window(parts,log)')),'digest expression'
 return {'heap_body_sha256':hashlib.sha256(heap.encode()).hexdigest(),'constructor_body_sha256':hashlib.sha256(new.encode()).hexdigest(),'digest_body_sha256':hashlib.sha256(digest.encode()).hexdigest()}
report=check(v,d);controls=[]
for label,vv,dd in [('reserve-width',v.replace('reserve(&mut out,n,log)','reserve(&mut out,n+1,log)'),d),('resize-value',v.replace('resize(&mut out,n,value,log,reply)','resize(&mut out,n,K::ZERO,log,reply)'),d),('constructor-next',v.replace('power:K::ONE,next:0','power:K::ONE,next:1'),d),('digest-slice',v,d.replace('hashv_window(parts,log).to_bytes()','hashv_window(&parts[1..],log).to_bytes()'))]:
 try:check(vv,dd)
 except AssertionError:controls.append(label)
 else:raise AssertionError('mutation accepted '+label)
report.update(status='PASS',frozen_revision=F,controls_rejected=controls,method='ruling (y) local-record source-fission call windows',retained=['std Vec reserve/resize value, capacity, ownership and allocation interpretation','P6/D188 semantic transport option A','runtime SHA digest value = H'],warning='Native call schedules do not prove allocator success or std implementation semantics; child value/frame laws remain explicit in Lean and trust inventory',native_input_sha256=hashlib.sha256((E/'NGC_NATIVE_INPUTS.json').read_bytes()).hexdigest())
(E/'NGC_SOURCE_ASSOCIATION.json').write_text(json.dumps(report,indent=1)+'\n');print('PASS source erasure and',len(controls),'mutations')
