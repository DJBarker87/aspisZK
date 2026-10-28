pub fn active_coordinate(mask:u16)->usize{match mask{6144=>0,6145=>1,4097=>2,2048=>3,2049=>4,26214=>5,1749=>6,_=>panic!("outside active basis")}}
pub fn add_word(a:u32,b:u32)->u32{let s=a+b;if s>=2147483647{s-2147483647}else{s}}
pub fn active_high_word(old:u32,high:u32,selected:bool)->u32{if selected{add_word(old,high)}else{old}}
pub fn pattern_word(old:u32,product:u32,selected:bool)->u32{if selected{add_word(old,product)}else{old}}
pub fn eq_factor_word(a:u32,b:u32,ab:u32)->u32{let p=2147483647u64;let s=(1u64+p-u64::from(a))%p;let s=(s+p-u64::from(b))%p;((s+u64::from(ab)+u64::from(ab))%p)as u32}
pub fn fields_word(value:u32)->Result<[u8;4],u8>{if value>=2147483647{Err(0)}else{Ok(value.to_le_bytes())}}
pub fn low_index(coordinate:usize,term:usize)->usize{let row=match coordinate{0=>[11,12,0,0,0,0,0,0],1=>[0,11,12,0,0,0,0,0],2=>[0,12,0,0,0,0,0,0],3=>[11,0,0,0,0,0,0,0],4=>[0,11,0,0,0,0,0,0],5=>[1,2,5,6,9,10,13,14],6=>[0,2,4,6,7,9,10,0],_=>panic!("coordinate")};row[term]}
pub fn low_count(coordinate:usize)->usize{[2,3,2,1,2,8,7][coordinate]}
pub fn add_product(raw:u64,product:u64)->u64{raw+product}
pub fn chunk_end(index:usize,end:usize)->usize{core::cmp::min(index+4,end)}
pub fn next_index(index:usize)->usize{index+1}
pub fn sub_word(a:u32,b:u32)->u32{((u64::from(a)+2147483647-u64::from(b))%2147483647)as u32}
pub fn factor_sum(first:u32,ab:u32)->u32{add_word(add_word(first,ab),ab)}
pub fn field_byte(value:u32,index:usize)->u8{value.to_le_bytes()[index]}
pub fn field_canonical(value:u32)->bool{value<2147483647}
pub fn header_gate(bytes:[u8;8],length:usize)->u8{if length!=320{1}else if bytes[0]!=65||bytes[1]!=83||bytes[2]!=81||bytes[3]!=56{2}else if bytes[4]!=1{3}else if bytes[5]!=0&&bytes[5]!=1{4}else if bytes[6]!=1{5}else if bytes[7]!=0{6}else{0}}
pub fn range_index(start:usize,end:usize,index:usize)->usize{assert!(start<=index&&index<end);index-start}
pub fn binding_matches(kind:bool,master:bool,lane:bool,output:bool,nullifier:bool,after:bool)->bool{kind&&master&&lane&&output&&nullifier&&after}
pub fn prefix_survives(index:usize,old_length:usize)->bool{index<old_length}
pub fn output_header(index:usize,kind:u8,lane:u8)->u8{match index{0=>65,1=>83,2=>82,3=>56,4=>1,5=>kind,6=>1,7=>lane,_=>panic!("header index")}}
