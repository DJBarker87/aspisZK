pub struct Dot{pub left:[u64;4],pub right:[u64;4],pub count:usize}
pub fn pack(d:Dot)->[u64;9]{[d.left[0],d.left[1],d.left[2],d.left[3],d.right[0],d.right[1],d.right[2],d.right[3],d.count as u64]}
pub fn unpack(w:[u64;9])->Dot{Dot{left:[w[0],w[1],w[2],w[3]],right:[w[4],w[5],w[6],w[7]],count:w[8] as usize}}
pub fn push_result(updated:[u64;9],index:usize,accepted:bool)->Result<(Dot,usize),u8>{if accepted{Ok((unpack(updated),index+1))}else{Err(0)}}
pub struct All{pub words:[u64;9],pub step:Result<(Dot,usize),u8>}
pub fn all_dots(w:[u64;9],index:usize,accepted:bool)->All{All{words:pack(unpack(w)),step:push_result(w,index,accepted)}}
