"""Append cfg(kani)-only checks after an exact frozen source prefix."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[2];p=root/'tools/pv-cbmid-20261027/hiding-with-harness.rs'
source=(root/'crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs').read_bytes()
suffix=b'''
#[cfg(all(kani,not(pv_cb_extract)))]
mod pv_cbm_checks {
    #[kani::proof]
    #[kani::unwind(25)]
    fn classifier_complete() {
        let row:usize=kani::any();let column:usize=kani::any();
        kani::assume(row<1024);kani::assume(column<16);
        assert_eq!(super::forest_aux_cell_is_used(row,column),crate::reference::aux_used(row,column));
    }
}
'''
p.write_bytes(source+suffix)
(root/'evidence/pv-cbmid-20261027/HARNESS-PREFIX.json').write_text(json.dumps(dict(original='crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs',original_size=len(source),original_sha256=hashlib.sha256(source).hexdigest(),staged_sha256=hashlib.sha256(source+suffix).hexdigest(),scope='Exact source prefix plus cfg(kani)-only child harness; private classifier check is a prerequisite, not a complete callback law.'),indent=2)+'\n')
