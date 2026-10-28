// Exact frozen native bodies; Error::Public is the only local error constructor.
#[derive(Debug)] enum Error {Public}
fn check_base_column(column:&[M31])->Result<(),Error> {
    if column.len()!=1024 {return Err(Error::Public);}
    let mut row=0;
    while row<1024 {
        if column[row].0>=P {return Err(Error::Public);}
        row+=1;
    }
    Ok(())
}
fn inactive_sum_m31(values:&[M31],masks:&[u16;64])->M31 {
    let mut sum=M31::ZERO;
    let mut row=0;
    while row<values.len() {
        if masks[row>>4]&(1<<(row&15))==0 {sum=sum.add(values[row]);}
        row+=1;
    }
    sum
}
