pub fn add_ref(x:u32,y:u32)->u32{let sum=x+y;if sum>=2147483647{sum-2147483647}else{sum}}
pub fn polynomial_step_ref(product:[u32;8],coefficient:[u32;8])->[u32;8]{let mut out=[0;8];let mut i=0;while i<8{out[i]=add_ref(product[i],coefficient[i]);i+=1;}out}
pub fn dot_step_ref(updated:[u64;9],index:usize,accepted:bool)->Result<([u64;9],usize),u8>{if accepted{Ok((updated,index+1))}else{Err(0)}}
pub fn round_ref(lhs:[u32;8],rhs:[u32;8],polynomial:[u32;8])->Result<[u32;8],u8>{if lhs!=rhs{Err(3)}else{Ok(polynomial)}}
pub struct All{pub polynomial:[u32;8],pub dot:Result<([u64;9],usize),u8>,pub round:Result<[u32;8],u8>}
pub fn all_refs(product:[u32;8],coefficient:[u32;8],updated:[u64;9],index:usize,accepted:bool,rhs:[u32;8],polynomial:[u32;8])->All{let lhs=polynomial_step_ref(product,coefficient);All{polynomial:lhs,dot:dot_step_ref(updated,index,accepted),round:round_ref(lhs,rhs,polynomial)}}
