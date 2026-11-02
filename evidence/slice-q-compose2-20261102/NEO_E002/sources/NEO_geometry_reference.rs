// Independent scalar dictionary for the exact source gather prefix.
// No field multiplication implementation: the caller installs the proven dictionary.
pub trait Ops {
 fn point(u:usize)->(u32,u32);
 fn line(u:usize)->u32;
 fn mul(x:u32,y:u32)->u32;
 fn double(x:u32)->u32;
 fn sub(x:u32,y:u32)->u32;
}
pub fn gather<O:Ops>(query:u32)->Result<[u32;5],u8> {
 let u=query as usize;
 if u>=262144 {return Err(0);}
 let (circle_x,circle_y)=O::point(u);
 let line_x=O::line(u/4*4);
 let line_y=O::line(u/4*4+3);
 let line_z=O::sub(O::double(O::mul(line_x,line_x)),1);
 let values=[circle_x,circle_y,line_x,line_y,line_z];
 if values.iter().any(|x|*x==0){return Err(0);}
 Ok(values)
}
