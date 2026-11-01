//! Safe indexed reference for the shipped bitwise pole scan, proof crate only.
use aspis_core::field::QM31;
fn equal(a:QM31,b:QM31)->bool {
    ((a.c0.a.0^b.c0.a.0)|(a.c0.b.0^b.c0.b.0)|
     (a.c1.a.0^b.c1.a.0)|(a.c1.b.0^b.c1.b.0))==0
}
pub fn all_slots_clear(values:&[[[QM31;2];2]],masks:&[u16;64],chi:QM31)->bool {
    let mut clear=true; let mut row=0usize;
    while row<values.len() {
        let active=(masks[row>>4]&(1u16<<(row&15)))!=0;
        clear=clear & !(active & equal(chi,values[row][0][0]));
        clear=clear & !(active & equal(chi,values[row][0][1]));
        clear=clear & !(active & equal(chi,values[row][1][0]));
        clear=clear & !(active & equal(chi,values[row][1][1]));
        row=row.wrapping_add(1);
    }
    clear
}
