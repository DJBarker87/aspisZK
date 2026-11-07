pub fn add_ref(x:u32,y:u32)->u32{let sum=x+y;if sum>=2147483647{sum-2147483647}else{sum}}
pub fn sub_ref(x:u32,y:u32)->u32{if x>=y{x-y}else{x+2147483647-y}}
pub fn point_ref(bit:[u32;4],carry:[u32;4],product:[u32;4])->[u32;4]{[sub_ref(add_ref(bit[0],carry[0]),add_ref(product[0],product[0])),sub_ref(add_ref(bit[1],carry[1]),add_ref(product[1],product[1])),sub_ref(add_ref(bit[2],carry[2]),add_ref(product[2],product[2])),sub_ref(add_ref(bit[3],carry[3]),add_ref(product[3],product[3]))]}
pub fn polynomial_step_ref(product:[u32;8],coefficient:[u32;8])->[u32;8]{[add_ref(product[0],coefficient[0]),add_ref(product[1],coefficient[1]),add_ref(product[2],coefficient[2]),add_ref(product[3],coefficient[3]),add_ref(product[4],coefficient[4]),add_ref(product[5],coefficient[5]),add_ref(product[6],coefficient[6]),add_ref(product[7],coefficient[7])]}
pub fn dot_step_ref(updated:[u64;9],index:usize,accepted:bool)->Result<([u64;9],usize),u8>{if accepted{Ok((updated,index+1))}else{Err(0)}}
pub fn round_ref(lhs:[u32;8],rhs:[u32;8],polynomial:[u32;8])->Result<[u32;8],u8>{if lhs!=rhs{Err(3)}else{Ok(polynomial)}}
pub struct All{pub point:[u32;4],pub polynomial:[u32;8],pub dot:Result<([u64;9],usize),u8>,pub round:Result<[u32;8],u8>}
pub fn all_refs(bit:[u32;4],carry:[u32;4],product:[u32;4],wide:[u32;8],coefficient:[u32;8],updated:[u64;9],index:usize,accepted:bool,rhs:[u32;8],polynomial:[u32;8])->All{let p=polynomial_step_ref(wide,coefficient);All{point:point_ref(bit,carry,product),polynomial:p,dot:dot_step_ref(updated,index,accepted),round:round_ref(p,rhs,polynomial)}}
