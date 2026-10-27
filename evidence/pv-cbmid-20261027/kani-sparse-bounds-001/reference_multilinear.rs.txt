//! Owned indexed P6 candidate, with the shipped sparse enumeration order.
//! Pure canonical QM31 inputs are required for the eventual native association.
use aspis_core::field::QM31;
pub fn evaluate(column:&[QM31], point:&[QM31;10])->Option<QM31> {
    if column.len()!=1024 {return None;}
    let mut trailing=0;
    while trailing<10 {
        let value=point[9-trailing];
        if value!=QM31::ZERO && value!=QM31::ONE {break;}
        trailing+=1;
    }
    let prefix_len=10-trailing;
    let mut suffix=0usize;
    let mut coordinate=prefix_len;
    while coordinate<10 {
        suffix=(suffix<<1)|usize::from(point[coordinate]==QM31::ONE);
        coordinate+=1;
    }
    let mut sum=QM31::ZERO;
    let mut prefix=0;
    while prefix<(1usize<<prefix_len) {
        let row=(prefix<<trailing)|suffix;
        let mut weight=QM31::ONE;
        let mut coordinate=0;
        while coordinate<prefix_len {
            let bit=(prefix>>(prefix_len-1-coordinate))&1;
            let value=point[coordinate];
            weight=weight.mul(if bit==0 {QM31::ONE.sub(value)} else {value});
            coordinate+=1;
        }
        sum=sum.add(weight.mul(column[row]));
        prefix+=1;
    }
    Some(sum)
}
