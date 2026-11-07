pub fn prefix(first:bool,second:bool,occupied:u32,inverse:u32,sentinel:u32,products:[u32;3],scan:bool)->u8{
 if !first || !second{1}else if occupied>=2147483647{2}else if inverse>=2147483647{3}else if products[0]!=0{4}else if products[1]!=occupied{5}else if products[2]!=0{6}else if scan{7}else if occupied==1&&sentinel==0{8}else{0}
}
