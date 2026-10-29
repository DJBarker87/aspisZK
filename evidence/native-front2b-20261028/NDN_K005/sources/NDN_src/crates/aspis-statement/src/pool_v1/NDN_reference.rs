pub fn active_coordinate(mask:u16)->usize{match mask{6144=>0,6145=>1,4097=>2,2048=>3,2049=>4,26214=>5,1749=>6,_=>panic!("outside active basis")}}
pub fn add_word(a:u32,b:u32)->u32{let s=a+b;if s>=2147483647{s-2147483647}else{s}}
pub fn active_high_word(old:u32,high:u32,selected:bool)->u32{if selected{add_word(old,high)}else{old}}
pub fn pattern_word(old:u32,product:u32,selected:bool)->u32{if selected{add_word(old,product)}else{old}}
pub fn eq_factor_word(a:u32,b:u32,ab:u32)->u32{let p=2147483647u64;let s=(1u64+p-u64::from(a))%p;let s=(s+p-u64::from(b))%p;((s+u64::from(ab)+u64::from(ab))%p)as u32}
pub fn fields_word(value:u32)->Result<[u8;4],u8>{if value>=2147483647{Err(0)}else{Ok(value.to_le_bytes())}}
