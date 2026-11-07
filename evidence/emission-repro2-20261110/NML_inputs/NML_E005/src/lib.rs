#[derive(Clone,Copy)] pub enum Error{Parse}
pub fn window_ref(left:[u32;8],right:[u32;4],after:[u64;8],count:usize,reject:bool)->(Result<(),Error>,[u64;8],usize,[u32;8],[u32;4]){
 let reply=if reject{Err(Error::Parse)}else{Ok(())};
 (reply,after,count,left,right)
}
