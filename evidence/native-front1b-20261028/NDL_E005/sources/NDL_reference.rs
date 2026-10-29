pub fn range_ref(i:usize)->(usize,usize){(i*32,(i+1)*32)}
pub fn decode_ref(bytes:&[u8])->[u32;8]{[
 u32::from_le_bytes([bytes[0],bytes[1],bytes[2],bytes[3]]),
 u32::from_le_bytes([bytes[4],bytes[5],bytes[6],bytes[7]]),
 u32::from_le_bytes([bytes[8],bytes[9],bytes[10],bytes[11]]),
 u32::from_le_bytes([bytes[12],bytes[13],bytes[14],bytes[15]]),
 u32::from_le_bytes([bytes[16],bytes[17],bytes[18],bytes[19]]),
 u32::from_le_bytes([bytes[20],bytes[21],bytes[22],bytes[23]]),
 u32::from_le_bytes([bytes[24],bytes[25],bytes[26],bytes[27]]),
 u32::from_le_bytes([bytes[28],bytes[29],bytes[30],bytes[31]])]}
pub fn field_ref(bytes:&[u8],i:usize)->[u32;8]{decode_ref(&bytes[i*32..(i+1)*32])}
pub fn add_word_ref(a:u32,b:u32)->u32{let s=a+b;if s>=2147483647{s-2147483647}else{s}}
pub fn add8_ref(a:[u32;8],b:[u32;8])->[u32;8]{[
 add_word_ref(a[0],b[0]),add_word_ref(a[1],b[1]),add_word_ref(a[2],b[2]),add_word_ref(a[3],b[3]),
 add_word_ref(a[4],b[4]),add_word_ref(a[5],b[5]),add_word_ref(a[6],b[6]),add_word_ref(a[7],b[7])]}
pub fn scalar_select_ref(s:usize)->(usize,usize){([0,3,2,1][s],s)}
pub fn qeq_ref(a:[u32;4],b:[u32;4])->bool{a[0]==b[0]&&a[1]==b[1]&&a[2]==b[2]&&a[3]==b[3]}
pub fn roweq_ref(a:[[u32;4];4],b:[[u32;4];4])->bool{qeq_ref(a[0],b[0])&&qeq_ref(a[1],b[1])&&qeq_ref(a[2],b[2])&&qeq_ref(a[3],b[3])}
pub fn guard_raw_ref(variant:u8,folds:usize,a:[[u32;4];4],b:[[u32;4];4],c:[[u32;4];4],d:[[u32;4];4])->bool{variant==1&&folds==2&&roweq_ref(a,b)&&roweq_ref(c,d)}

pub fn double_observed_ref(p0:[u32;4],p1:[u32;4])->[u32;4]{[sub_ref(add_ref(p0[0],p1[0]),1),sub_ref(add_ref(p0[1],p1[1]),0),sub_ref(add_ref(p0[2],p1[2]),0),sub_ref(add_ref(p0[3],p1[3]),0)]}

fn add_ref(x:u32,y:u32)->u32 {let s=x+y;if s>=2147483647{s-2147483647}else{s}}

fn sub_ref(x:u32,y:u32)->u32 {let s=x+2147483647-y;if s>=2147483647{s-2147483647}else{s}}

pub fn forward_ref(start:usize,end:usize)->(bool,usize,usize,usize){if start<end{(true,start,start+1,end)}else{(false,0,start,end)}}
pub fn reverse_ref(start:usize,end:usize)->(bool,usize,usize,usize){if start<end{(true,end-1,start,end-1)}else{(false,0,start,end)}}
pub fn finish_ref(reply:[u32;8])->[u32;8]{reply}
pub fn quarter_ref()->u32{536870912}
pub fn perm_ref(s:usize)->usize{[0,3,2,1][s]}
