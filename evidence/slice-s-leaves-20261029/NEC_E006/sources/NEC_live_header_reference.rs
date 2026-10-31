pub const LIVE_BINDING:[u8;32]=[65,83,80,80,65,73,82,49,1,20,21,7,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
pub fn live_header_ref(length:usize,bytes:&[u8;48])->u8 {
 if length!=800{return 1;}
 if bytes[0]!=65 || bytes[1]!=83 || bytes[2]!=80 || bytes[3]!=76 || bytes[4]!=73 || bytes[5]!=86 || bytes[6]!=69 || bytes[7]!=49{return 2;}
 if bytes[8]!=1{return 3;}
 if bytes[9]!=0 || bytes[10]!=0 || bytes[11]!=0 || bytes[12]!=0 || bytes[13]!=0 || bytes[14]!=0 || bytes[15]!=0{return 4;}
 if bytes[16]!=65 || bytes[17]!=83 || bytes[18]!=80 || bytes[19]!=80 || bytes[20]!=65 || bytes[21]!=73 || bytes[22]!=82 || bytes[23]!=49 || bytes[24]!=1 || bytes[25]!=20 || bytes[26]!=21 || bytes[27]!=7 || bytes[28]!=1 || bytes[29]!=1 || bytes[30]!=1 || bytes[31]!=1 || bytes[32]!=0 || bytes[33]!=0 || bytes[34]!=0 || bytes[35]!=0 || bytes[36]!=0 || bytes[37]!=0 || bytes[38]!=0 || bytes[39]!=0 || bytes[40]!=0 || bytes[41]!=0 || bytes[42]!=0 || bytes[43]!=0 || bytes[44]!=0 || bytes[45]!=0 || bytes[46]!=0 || bytes[47]!=0{return 5;}
 0
}
