pub fn scalar(raw:u64,limb:u32,basis:u32,flush:bool)->u64 {
 let sum=raw+u64::from(limb)*u64::from(basis);
 if flush{(sum&0x7fff_ffff)+(sum>>31)}else{sum}
}
pub fn row_ref(row:[u64;4],power:[u32;4],basis:u32,flush:bool)->[u64;4]{
 [scalar(row[0],power[0],basis,flush),scalar(row[1],power[1],basis,flush),scalar(row[2],power[2],basis,flush),scalar(row[3],power[3],basis,flush)]
}
