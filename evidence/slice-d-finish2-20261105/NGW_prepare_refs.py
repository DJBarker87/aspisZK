from pathlib import Path
E=Path(__file__).resolve().parent
s='pub fn sub_ref(x:u32,y:u32)->u32{if x>=y{x-y}else{x+2147483647-y}}\n'
s+='pub fn one_sub(a:[u32;4])->[u32;4]{[sub_ref(1,a[0]),sub_ref(0,a[1]),sub_ref(0,a[2]),sub_ref(0,a[3])]}\n'
s+='pub struct FactorPacket{pub left:[[u32;4];4],pub right:[[u32;4];4],pub row:[[u32;4];4]}\n'
s+='pub fn factor_ref(a:[u32;4],b:[u32;4],replies:[[u32;4];4])->FactorPacket{let aa=one_sub(a);let bb=one_sub(b);FactorPacket{left:[aa,a,aa,a],right:[bb,bb,b,b],row:replies}}\n'
s+='pub struct CirclePacket{pub row:[[u32;4];4],pub next:[u32;4]}\n'
s+='pub fn circle_ref(x:[u32;4],y:[u32;4],product:[u32;4],next:[u32;4])->CirclePacket{CirclePacket{row:[[1,0,0,0],x,y,product],next}}\n'
s+='pub struct All{pub factor:FactorPacket,pub circle:CirclePacket}\n'
s+='pub fn all_factors(a:[u32;4],b:[u32;4],replies:[[u32;4];4],next:[u32;4])->All{All{factor:factor_ref(a,b,replies),circle:circle_ref(a,b,replies[0],next)}}\n'
(E/'NGW_factor_reference.rs.txt').write_text(s)
s='pub struct Dot{pub left:[u64;4],pub right:[u64;4],pub count:usize}\n'
s+='pub fn pack(d:Dot)->[u64;9]{[d.left[0],d.left[1],d.left[2],d.left[3],d.right[0],d.right[1],d.right[2],d.right[3],d.count as u64]}\n'
s+='pub fn unpack(w:[u64;9])->Dot{Dot{left:[w[0],w[1],w[2],w[3]],right:[w[4],w[5],w[6],w[7]],count:w[8] as usize}}\n'
s+='pub fn push_result(updated:[u64;9],index:usize,accepted:bool)->Result<(Dot,usize),u8>{if accepted{Ok((unpack(updated),index+1))}else{Err(0)}}\n'
s+='pub struct All{pub words:[u64;9],pub step:Result<(Dot,usize),u8>}\n'
s+='pub fn all_dots(w:[u64;9],index:usize,accepted:bool)->All{All{words:pack(unpack(w)),step:push_result(w,index,accepted)}}\n'
(E/'NGW_dot_reference.rs.txt').write_text(s)
p=E/'NGW_extract.py';s=p.read_text().replace("'NGW_HelperRef':'crate::all_refs'", "'NGW_HelperRef':'crate::all_refs','NGW_FactorRef':'crate::all_factors','NGW_DotRef':'crate::all_dots'");p.write_text(s)
p=E/'NGW_run.py';s=p.read_text();old="(E/('NGW_double_reference.rs.txt' if target=='NGW_DoubleRef' else 'NGW_helper_reference.rs.txt' if target=='NGW_HelperRef' else 'NGW_references.rs.txt')).read_text()";new="(E/({'NGW_FactorRef':'NGW_factor_reference.rs.txt','NGW_DotRef':'NGW_dot_reference.rs.txt','NGW_HelperRef':'NGW_helper_reference.rs.txt','NGW_DoubleRef':'NGW_double_reference.rs.txt'}.get(target,'NGW_references.rs.txt'))).read_text()";assert old in s;s=s.replace(old,new);p.write_text(s)
