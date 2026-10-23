from pathlib import Path
E=Path(__file__).resolve().parent.parent;O=E.parent/'prover-commit49-20261022'
p=E/'dot-owner/lib.rs';s=p.read_text();s+='\n'+(O/'channel-owner/lib.rs').read_text().split('pub mod channels')[1].join(['pub mod channels','']) if False else ''
s+='\n'+(O/'channel-owner/lib.rs').read_text()[(O/'channel-owner/lib.rs').read_text().index('pub mod channels'):]
s+='''
pub mod totals50 {
use super::{field::M31,channels};
pub fn channel(a:[[[M31;3];3];3],b:[[[M31;3];3];3],c:usize,h:usize)->u64 {
 channels::sum([a[0][c][h],a[1][c][h],a[2][c][h]],
               [b[0][c][h],b[1][c][h],b[2][c][h]],0,3,0)
}
pub fn all(a:[[[M31;3];3];3],b:[[[M31;3];3];3])->[[u64;3];3] {
 [ [channel(a,b,0,0),channel(a,b,0,1),channel(a,b,0,2)],
   [channel(a,b,1,0),channel(a,b,1,1),channel(a,b,1,2)],
   [channel(a,b,2,0),channel(a,b,2,1),channel(a,b,2,2)] ]
}
}
''';p.write_text(s)
s=(E/'harness/extract-dot.py').read_text().replace('crate::dot50','crate::totals50').replace('dot-owner-charon-v1','dot-owner-charon-v2').replace('dot-owner-aeneas-v1','dot-owner-aeneas-v2');(E/'harness/extract-totals.py').write_text(s)
s=(E/'harness/bind-dot.py').read_text().replace('Dot50.lean','Totals50.lean').replace('dot-callee-binding','totals-callee-binding').replace('old.update(declarations(L/"AspisR1ProducerRelease47/Basis.lean"))','old.update(declarations(L/"AspisR1ProducerRelease47/Channels49.lean"))\nold.update(declarations(L/"AspisR1ProducerRelease47/Basis.lean"))').replace('import AspisR1ProducerRelease47.Funs\\n','import AspisR1ProducerRelease47.Channels49\\n');(E/'harness/bind-totals.py').write_text(s)
