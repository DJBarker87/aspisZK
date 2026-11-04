use aspis_core::field::M31;
use aspis_core::r0::domain;
#[derive(Clone,Copy)]
pub enum Error{Query}
#[derive(Clone,Copy)]
pub struct NFB_RowCall{kind:u8,a:u32,b:u32,reply:u32,reply2:u32}
pub struct NFB_RowLog{calls:[NFB_RowCall;4],len:usize}
fn NFB_row_call(log:&mut NFB_RowLog,kind:u8,a:u32,b:u32,reply:u32,reply2:u32){
 log.calls[log.len]=NFB_RowCall{kind,a,b,reply,reply2};log.len+=1;
}
// Local opaque-call-log form: no native field multiplication is evaluated.
fn NFB_row_product(a:M31,b:M31,reply:M31,log:&mut NFB_RowLog)->M31{
 NFB_row_call(log,4,a.0,b.0,reply.0,0);reply
}
pub fn NFB_row(query:u32,replies:[u32;5],log:&mut NFB_RowLog)->Result<[M31;5],Error>{
 let u=query as usize;
 let fibre=domain::FibreIndex::new(u).map_err(|_|Error::Query)?;
 NFB_row_call(log,1,fibre.get() as u32,0,replies[0],replies[1]);
 let domain::Point{x:circle_x,y:circle_y}=domain::Point{x:M31(replies[0]),y:M31(replies[1])};
 let left=domain::FibreIndex::new(u/4*4).map_err(|_|Error::Query)?;
 NFB_row_call(log,2,left.get() as u32,0,replies[2],0);
 let line_x=M31(replies[2]);
 let right=domain::FibreIndex::new(u/4*4+3).map_err(|_|Error::Query)?;
 NFB_row_call(log,3,right.get() as u32,0,replies[3],0);
 let line_y=M31(replies[3]);
 let line_z=NFB_row_product(line_x,line_x,M31(replies[4]),log).double().sub(M31::ONE);
 let values=[circle_x,circle_y,line_x,line_y,line_z];
 Ok(values)
}
