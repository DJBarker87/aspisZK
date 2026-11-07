pub type Digest=[u32;8];
pub struct Packet{pub left:[Digest;7],pub right:[Digest;7],pub out:Digest,pub calls:usize}
pub fn compose(roots:[Digest;8],replies:[Digest;7])->Packet{Packet{left:[roots[0],roots[2],roots[4],roots[6],replies[0],replies[2],replies[4]],right:[roots[1],roots[3],roots[5],roots[7],replies[1],replies[3],replies[5]],out:replies[6],calls:7}}
