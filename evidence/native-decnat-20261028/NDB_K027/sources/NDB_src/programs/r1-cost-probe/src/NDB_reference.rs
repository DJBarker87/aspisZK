// Safe reference for the frozen TX2 decoders. No external decoder calls.
// All wrapper failures map to InvalidAccountData, represented by Err(()).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Identity { pub pool:[u8;32],pub asset_mint:[u8;32],pub token_program:[u8;32],pub asset_id:u32,pub deployment_domain:[u8;32] }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Policy {pub flags:u8,pub registry_program:[u8;32],pub registry_authority:[u8;32],pub policy_binding:[u8;32]}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Master {pub bump:u8,pub identity:Identity,pub verifier_policy:Policy,pub initialized_lane_mask:u8,pub has_checkpoint:bool,pub next_checkpoint_sequence:u64,pub last_checkpoint_lane_sequences:[u64;8]}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Checkpoint {pub bump:u8,pub master:[u8;32],pub deployment_domain:[u8;32],pub checkpoint_sequence:u64,pub global_root:[u32;8],pub lane_sequences:[u64;8]}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Lane {pub bump:u8,pub master:[u8;32],pub lane_id:u8,pub next_leaf_index:u64,pub root:[u32;8],pub frontier:[[u32;8];20]}
pub const BINDING:[u8;32]=[65,83,80,73,83,70,79,82,69,83,84,56,2,2,2,8,1,20,1,0,0,0,0,0,0,0,0,0,0,0,0,0];
pub const EMPTY:[[u32;8];21]=[[1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,1155026732],[141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536],[1119858538,128294437,939091034,659145897,1933666768,903679201,1182639487,1398246146],[1057897051,1132946363,794377079,1971564389,1255722275,926653737,2031728153,2024887573],[1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616],[1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592],[244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587],[673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631],[27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718],[1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885],[418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893],[986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062],[2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184],[260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542],[1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983],[1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477],[1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353],[1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413],[1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803],[19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443],[1201428963,1296676114,441891487,1910121140,602621674,1294160489,1878016864,855887413]];
pub fn equal(b:&[u8],v:&[u8])->bool {if b.len()!=v.len(){return false} let mut i=0;while i<b.len(){if b[i]!=v[i]{return false}i+=1;}true}
pub fn zero(b:&[u8])->bool {let mut i=0;while i<b.len(){if b[i]!=0{return false}i+=1;}true}
pub fn bytes32(b:&[u8],s:usize)->[u8;32]{let mut a=[0u8;32];let mut i=0;while i<32{a[i]=b[s+i];i+=1;}a}
pub fn word64(b:&[u8],s:usize)->u64{u64::from_le_bytes([b[s],b[s+1],b[s+2],b[s+3],b[s+4],b[s+5],b[s+6],b[s+7]])}
pub fn word32(b:&[u8],s:usize)->u32{u32::from_le_bytes([b[s],b[s+1],b[s+2],b[s+3]])}
pub fn digest(b:&[u8],s:usize)->Result<[u32;8],()>{let mut out=[0u32;8];let mut i=0;while i<8{let x=word32(b,s+4*i);if x>=2147483647{return Err(())}out[i]=x;i+=1;}Ok(out)}
pub fn eq_digest(a:&[u32;8],b:&[u32;8])->bool{let mut i=0;while i<8{if a[i]!=b[i]{return false}i+=1;}true}
pub fn identity(b:&[u8])->Result<Identity,()>{
 if b.len()!=144 || !equal(&b[..4],b"ASPI") || b[4]!=1 || !zero(&b[5..8]) || !zero(&b[108..112]) {return Err(())}
 let asset_id=word32(b,104);if asset_id>=2147483647{return Err(())}
 Ok(Identity{pool:bytes32(b,8),asset_mint:bytes32(b,40),token_program:bytes32(b,72),asset_id,deployment_domain:bytes32(b,112)})
}
pub fn valid_policy(p:&Policy)->bool{
 if p.flags & !3 !=0 || zero(&p.registry_program) || zero(&p.policy_binding) {return false}
 let immutable=p.flags&1!=0;let deployment=p.flags&2!=0;
 if deployment && !immutable{return false}
 immutable==zero(&p.registry_authority)
}
pub fn policy(b:&[u8])->Result<Policy,()>{
 if b.len()!=104 || !equal(&b[..4],b"ASPP") || b[4]!=1 || !zero(&b[6..8]){return Err(())}
 let p=Policy{flags:b[5],registry_program:bytes32(b,8),registry_authority:bytes32(b,40),policy_binding:bytes32(b,72)};
 if !valid_policy(&p){return Err(())}Ok(p)
}
pub fn valid_master(m:&Master)->bool{
 if zero(&m.identity.pool)||zero(&m.identity.asset_mint)||zero(&m.identity.token_program)||zero(&m.identity.deployment_domain)||!valid_policy(&m.verifier_policy){return false}
 if !valid_sequences(&m.last_checkpoint_lane_sequences){return false}
 let nonzero=!zero_sequences(&m.last_checkpoint_lane_sequences);
 if (!m.has_checkpoint&&(m.next_checkpoint_sequence!=0||nonzero))||(m.has_checkpoint&&m.next_checkpoint_sequence==0){return false}true
}
pub fn decode_master_ref(b:&[u8])->Result<Box<Master>,()>{
 if b.len()!=384{return Err(())}
 if !equal(&b[..4],b"ASM8")||b[4]!=2||b[5]!=8||b[6]!=1||!zero(&b[50..64])||!zero(&b[312..320])||!equal(&b[8..40],&BINDING){return Err(())}
 let has_checkpoint=match b[49]{0=>false,1=>true,_=>return Err(())};
 let id=identity(&b[64..208])?;let p=policy(&b[208..312])?;
 let seq=sequences(b,320);
 let m=Master{bump:b[7],identity:id,verifier_policy:p,initialized_lane_mask:b[48],has_checkpoint,next_checkpoint_sequence:word64(b,40),last_checkpoint_lane_sequences:seq};
 if !valid_master(&m){return Err(())}Ok(Box::new(m))
}
pub fn decode_checkpoint_ref(b:&[u8])->Result<Box<Checkpoint>,()>{
 if b.len()!=192{return Err(())}
 if !equal(&b[..4],b"ASC8")||b[4]!=2||b[5]!=8||b[6]!=1||!zero(&b[176..]){return Err(())}
 let master=bytes32(b,8);let deployment_domain=bytes32(b,40);
 if zero(&master)||zero(&deployment_domain){return Err(())}
 let global_root=digest(b,80)?;
 let seq=sequences(b,112);if !valid_sequences(&seq){return Err(())}
 Ok(Box::new(Checkpoint{bump:b[7],master,deployment_domain,checkpoint_sequence:word64(b,72),global_root,lane_sequences:seq}))
}
pub fn decode_lane_ref(b:&[u8])->Result<Box<Lane>,()>{
 if b.len()!=768{return Err(())}
 if !equal(&b[..4],b"ASL8")||b[4]!=2||b[5]>=8||b[6]!=8||b[7]!=20||!equal(&b[8..40],&BINDING)||!zero(&b[73..80]){return Err(())}
 let master=bytes32(b,40);if zero(&master){return Err(())}
 let tree=&b[80..];
 if !equal(&tree[..4],b"ASPT")||tree[4]!=1||tree[5]!=20||tree[6]!=3||tree[7]!=1{return Err(())}
 let next_leaf_index=word64(tree,8);if next_leaf_index>1048576{return Err(())}
 let root=digest(tree,16)?;let frontier=decode_frontier(tree,next_leaf_index)?;
 if next_leaf_index==0&&!eq_digest(&root,&EMPTY[20]){return Err(())}
 Ok(Box::new(Lane{bump:b[72],master,lane_id:b[5],next_leaf_index,root,frontier}))
}
// Include the Option language item required by pinned Aeneas loop-return lowering.
pub fn option_item(x:Option<u8>)->Option<u8>{x}

pub fn sequences(b:&[u8],start:usize)->[u64;8]{let mut seq=[0u64;8];let mut i=0;while i<8{seq[i]=word64(b,start+8*i);i+=1;}seq}
pub fn valid_sequences(seq:&[u64;8])->bool{let mut i=0;while i<8{if seq[i]>1048576{return false}i+=1;}true}
pub fn zero_sequences(seq:&[u64;8])->bool{let mut i=0;while i<8{if seq[i]!=0{return false}i+=1;}true}
pub fn decode_frontier(tree:&[u8],next:u64)->Result<[[u32;8];20],()>{let mut frontier=[[0u32;8];20];let mut level=0;while level<20{let node=digest(tree,48+32*level)?;frontier[level]=node;if (next>>level)&1==0&&!eq_digest(&node,&EMPTY[level]){return Err(())}level+=1;}Ok(frontier)}
