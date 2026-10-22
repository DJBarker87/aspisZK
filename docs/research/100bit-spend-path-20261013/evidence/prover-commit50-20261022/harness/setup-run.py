from pathlib import Path
E=Path(__file__).resolve().parent.parent;O=E.parent/'prover-commit49-20261022'
p=E/'dot-owner/lib.rs';s=p.read_text();old=(O/'reconstruction-owner/lib.rs').read_text();s+='\n'+old[old.index('pub mod reconstruction'):];s+='''
pub mod run50 {
use super::{field::QM31 as K,dot50,totals50,reconstruction};
pub fn prepare3(x:[K;3])->[[[super::field::M31;3];3];3] {
 [dot50::prepare(x[0]),dot50::prepare(x[1]),dot50::prepare(x[2])]
}
pub fn run(x:[K;3],y:[K;3])->K {
 let a=prepare3(x);let b=prepare3(y);
 reconstruction::q(totals50::all(a,b))
}
}
''';p.write_text(s)
s=(E/'harness/extract-totals.py').read_text().replace('crate::totals50','crate::run50').replace('charon-v2','charon-v3').replace('aeneas-v2','aeneas-v3');(E/'harness/extract-run.py').write_text(s)
s=(E/'harness/bind-totals.py').read_text().replace('Totals50.lean','Run50.lean').replace('totals-callee-binding','run-callee-binding')
s=s.replace('old,new=declarations(retained),declarations(source)','old,new=declarations(retained),declarations(source)\nfor f in ["Dot50", "Totals50", "Reconstruction49"]:old.update(declarations(L/("AspisR1ProducerRelease47/"+f+".lean")))')
s=s.replace('import AspisR1ProducerRelease47.Channels49','import AspisR1ProducerRelease47.Dot50\nimport AspisR1ProducerRelease47.Totals50\nimport AspisR1ProducerRelease47.Reconstruction49');(E/'harness/bind-run.py').write_text(s)
