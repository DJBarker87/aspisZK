//! Owned, alias-free candidate for V228. Native correspondence remains OPEN.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct Cell { pub row: u16, pub column: u8 }

pub fn free(row: usize, column: usize) -> bool {
    if row < 912 {
        return row % 16 >= 13;
    }
    if row < 1008 {
        let local = row % 16;
        let base = local == 1 || local == 5 || local == 9 || local == 13;
        let successor = local == 2 || local == 6 || local == 10 || local == 14;
        return !((base && column <= 8) || successor);
    }
    let local = row - 1008;
    let whole = local == 0 || local == 1 || local == 2 || local == 3 || local == 4
        || local == 5 || local == 8 || local == 9 || local == 12 || local == 14;
    let used = (whole && column <= 10) || (local == 6 && column < 3)
        || (local == 7 && column < 2) || (local == 10 && column < 10);
    !used
}

pub fn cells() -> ([Cell;3803],usize) {
    let mut out = [Cell { row: 0, column: 0 };3803];
    let mut count = 0usize;
    let mut column = 0usize;
    while column < 16 {
        let mut row = 0usize;
        while row < 1024 {
            if free(row,column) {
                out[count] = Cell { row: row as u16, column: column as u8 };
                count += 1;
            }
            row += 1;
        }
        column += 1;
    }
    (out,count)
}
