"""Bind the complete deployed static M31 inverse backend, not pointer Kani."""
from pathlib import Path
import hashlib,json,runpy
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028')
S=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028/src')
a=runpy.run_path(str(D/'range-source.py'));span,tokens,sha=a['span'],a['tokens'],a['sha']
p=S/'crates/aspis-core/src/field.rs';s=p.read_text()
expected={
'square_n':('fn square_n(', 'fn square_n(mut value:M31,count:usize)->M31 { for _ in 0..count {value=value.mul(value);} value }','V265Inverse.square_count'),
'inv':('impl M31 {','''pub fn inv(self)->M31 {
 #[cfg(feature="r0-op-count")] let _count=crate::r0_op_count::enter(crate::r0_op_count::Op::FInv);
 assert!(self.0!=0,"inverse of zero");
 let t2=self.mul(self).mul(self);
 let t4=square_n(t2,2).mul(t2);
 let t8=square_n(t4,4).mul(t4);
 let t16=square_n(t8,8).mul(t8);
 let t24=square_n(t16,8).mul(t8);
 let t28=square_n(t24,4).mul(t4);
 let t29=t28.mul(t28).mul(self);
 let t30=t29.mul(t29);
 t30.mul(t30).mul(self)
}''','V265Inverse.source'),
'CM31.inv':('impl CM31 {','pub fn inv(self)->CM31 { self.inv_with(M31::inv) }','V265Inverse.cm_source')}
records=[]
for key,(context,body,law) in expected.items():
 marker='fn square_n(' if key=='square_n' else 'pub fn inv('
 actual=span(s,context,marker)
 assert tokens(actual)==tokens(body),(key,actual)
 bad=body.replace('value.mul(value)','value.add(value)',1) if key=='square_n' else body.replace('M31::inv','M31::neg',1) if key=='CM31.inv' else body.replace('square_n(t2,2)','square_n(t2,3)',1)
 assert tokens(actual)!=tokens(bad),key
 records.append(dict(key=key,source_body=actual,owned_pattern=body,law='R1Z.PV_RDCD3_'+law,negative_control='changed operation/count/dispatch rejected'))
features=json.load(open(D/'deployed-client-features.json'))
core=[x for x in features if x['name']=='aspis-core'];assert core
assert all('ct-host-prover' in x['features'] and 'r0-op-count' not in x['features'] for x in core)
assert all(not x['profile']['debug_assertions'] and not x['profile']['overflow_checks'] for x in features)
j=dict(source=dict(path=str(p),sha256=sha(p.read_bytes())),bodies=records,feature_graph_sha256=sha((D/'deployed-client-features.json').read_bytes()),profile='deployed release, rust1.94.1 native; assert! is unconditional, op-count disabled',range_binding_sha256=sha((D/'range-source-result.json').read_bytes()),scope='Static M31 backend source binding only. Complete circle law, library disposition, source cohort and native finite evidence remain required.',pointer_kani='QUARANTINED under r-double-prime; no Kani run or credit',composition='Reclassification within existing Aeneas/Rust/compiler trust, never endpoint premise removal')
(D/'v265-source-result.json').write_text(json.dumps(j,indent=2)+'\n');print('Three complete inverse/loop/static-dispatch bodies matched with rejecting controls; op-count disabled')
