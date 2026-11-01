
pub fn aux_used(row:usize,column:usize)->bool {
    if row<912 {return false;}
    if row<1008 {
        let delta=row-912;
        return ((delta&3)==1 && column<=8) || (delta&3)==2;
    }
    let translated=row-48;
    let mut value=0;
    while value<3 {
        let base=960+2*value;
        if (translated==base || translated==base+1 || translated==(base^12)) && column<=10 {return true;}
        value+=1;
    }
    (translated==966 && column<3) || (translated==967 && column<2) ||
    (translated==969 && column<=10) || (translated==970 && column<10)
}
