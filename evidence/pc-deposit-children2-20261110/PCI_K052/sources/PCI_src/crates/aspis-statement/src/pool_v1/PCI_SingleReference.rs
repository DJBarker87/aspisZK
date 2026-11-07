pub struct Single{pub tag:u8,pub first:[u32;8],pub occupied:u32,pub second:[u32;8],pub inverse:u32}
pub fn single_reference(d:[u32;8])->Single{
 if d[0]<2147483647&&d[1]<2147483647&&d[2]<2147483647&&d[3]<2147483647&&d[4]<2147483647&&d[5]<2147483647&&d[6]<2147483647&&d[7]<2147483647{Single{tag:0,first:d,occupied:0,second:[0;8],inverse:0}}
 else{Single{tag:1,first:[0;8],occupied:0,second:[0;8],inverse:0}}
}
