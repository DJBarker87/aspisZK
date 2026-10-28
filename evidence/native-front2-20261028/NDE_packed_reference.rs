pub fn matrix_cell_ref(a:u32,b:u32,c:u32,d:u32,row:usize)->u64{
 let a=u64::from(a);let b=u64::from(b);let c=u64::from(c);let d=u64::from(d);
 match row{0=>2*a+3*b+c+d,1=>a+2*b+3*c+d,2=>a+b+2*c+3*d,3=>3*a+b+c+2*d,_=>panic!("matrix row")}
}
pub fn scan_step_ref(flag:bool,cell:u64,bound:u64,row:usize,limb:usize)->(bool,usize,usize,bool){
 if limb<4{(flag&(cell<bound),row,limb+1,false)}else{(flag,row+1,limb,true)}
}
pub fn packed_after_ref(local:[[u64;4];4],bound:u64)->[u64;4]{
 [local[0][0]+5*bound-local[1][1]+2*local[2][2]-local[2][3]-local[3][2]-2*local[3][3],
 local[0][1]+local[1][0]+local[2][2]+2*local[2][3]+2*local[3][2]+bound-local[3][3],
 local[0][2]+2*bound-local[1][3]+local[2][0]-local[3][1],
 local[0][3]+local[1][2]+local[2][1]+local[3][0]]
}
