fn back_cell(original:u32,update:u32,index:usize,remaining:usize,last:u32)->u32 {
    if remaining>0 && index==remaining-1 {last}
    else if remaining>0 && index<remaining-1 {update}
    else {original}
}
pub fn back_frame(data:&[u32;8],remaining:usize,updates:&[u32;8],last:u32)->(Option<u32>,[u32;8],usize) {
    let old=if remaining==0 {None}else{Some(data[remaining-1])};
    let next=if remaining==0 {0}else{remaining-1};
    let result=[
        back_cell(data[0],updates[0],0,remaining,last),
        back_cell(data[1],updates[1],1,remaining,last),
        back_cell(data[2],updates[2],2,remaining,last),
        back_cell(data[3],updates[3],3,remaining,last),
        back_cell(data[4],updates[4],4,remaining,last),
        back_cell(data[5],updates[5],5,remaining,last),
        back_cell(data[6],updates[6],6,remaining,last),
        back_cell(data[7],updates[7],7,remaining,last),
    ];
    (old,result,next)
}

fn main(){
let data=[0,0,0,0,0,0,268435476,16];
let updates=[15016073,1086431253,5242880,750403596,2752530,1178599424,20,0];
let remaining=8; let last=2050; let mut actual=data;
let read;
{ let mut iter=actual[..remaining].iter_mut();
read=iter.next_back().map(|word|{let old=*word; *word=last; old});
let rest=iter.into_slice(); let n=if remaining==0{0}else{remaining-1};
assert_eq!(rest.len(),n); if remaining>0 {rest.copy_from_slice(&updates[..n]);}}
let expected=back_frame(&data,remaining,&updates,last);
println!("read={read:?}; actual={actual:?}; expected={expected:?}");
assert_eq!(read,expected.0); assert_eq!(actual,expected.1);
}
