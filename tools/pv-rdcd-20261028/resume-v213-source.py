"""Independent closure/constructor source-law binding, not an original checker.
Preserve all four CT calls, both coordinates and the captureless drop boundary.
"""
from pathlib import Path
import re,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');S=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028/src');E=D/'resume-v213-source';E.mkdir(exist_ok=True)
def sha(b):return hashlib.sha256(b).hexdigest()
def tok(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S))
def span(s,marker,last=False):
 a=s.rindex(marker) if last else s.index(marker);b=s.index('{',a);e=b+1;depth=1
 while depth:depth+=(s[e]=='{')-(s[e]=='}');e+=1
 return s[a:e]
p=S/'crates/aspis-core/src/field/wide_exact.rs';text=p.read_text();body=span(text,'fn canonical_qm31(',True)
expected='''fn canonical_qm31(value: QM31) -> QM31 {
let reduce = |x: M31| M31(super::ct::reduce64(x.0 as u64));
QM31 { c0: CM31 { a: reduce(value.c0.a), b: reduce(value.c0.b) }, c1: CM31 { a: reduce(value.c1.a), b: reduce(value.c1.b) } }
}'''
assert tok(body)==tok(expected)
a=text.rindex('fn canonical_qm31(');prefix=text[max(0,a-80):a];assert '#[cfg(feature = "ct-host-prover")]' in prefix
new=span(text,'pub fn new(c0: QM31, c1: QM31) -> Self')
assert tok(new)==tok('''pub fn new(c0: QM31, c1: QM31) -> Self { Self { c0: canonical_qm31(c0), c1: canonical_qm31(c1), } }''')
refs=json.load(open(D/'resume-extraction-plans.json'));ref=refs['V213REF']['wrapper'];rb=span(ref,'pub fn canonical_qm31(')
expectedref='''pub fn canonical_qm31(x: QM31) -> QM31 { QM31 { c0: CM31 { a: M31(ct::reduce64(x.c0.a.0 as u64)), b: M31(ct::reduce64(x.c0.b.0 as u64)), }, c1: CM31 { a: M31(ct::reduce64(x.c1.a.0 as u64)), b: M31(ct::reduce64(x.c1.b.0 as u64)), }, } }'''
assert tok(rb)==tok(expectedref)
record=dict(row='V213',source_path=str(p),source_sha256=sha(p.read_bytes()),source_body=body,constructor_body=new,reference_body=rb,reference_source_pin=refs['V213REF']['wrapper_source_sha256'],cfg='ct-host-prover=true; release; assertions/overflow checks off',source_call_order=['c0.a','c0.b','c1.a','c1.b'],difference='captureless scalar closure versus four direct identical ct::reduce64 calls; two helper applications in WideExact::new',laws=['PV_RDCD_CanonicalSource.environment_unique','PV_RDCD_CanonicalSource.drop_frame','PV_RDCD_CanonicalSource.reference'],primitive_boundary='Rust captureless closure application/empty automatic drop, scalar cast/arithmetic and compiler cohort; global carrier/world and L1/L2/L3 retained',qualifications=['Supplemental explicit source proof, not a recovered standalone original structural checker.','No Kani result used or re-credited; no generated output is edited and no extractor guard disabled.','All raw QM31 field values admitted by the source proof; native cases alone remain finite validation.'])
(E/'binding.json').write_text(json.dumps(record,indent=2)+'\n');print('Exact CT closure body and constructor bound to the unchanged direct reference; no arithmetic replacement')
