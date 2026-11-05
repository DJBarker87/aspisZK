struct InterpolationLog{count:usize,args:[[u32;2];3],products:[u64;3],reductions:usize,reduced:u64,reply:M31}
fn raw_product(a:u32,b:u32,log:&mut InterpolationLog)->u64{let i=log.count;log.count+=1;log.args[i]=[a,b];log.products[i]}
fn raw_reduce(x:u64,log:&mut InterpolationLog)->M31{log.reductions+=1;log.reduced=x;log.reply}
include!("NHU_interpolation_body.rs");
#[kani::proof]#[kani::unwind(32)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_interpolation(){let input:[u32;6]=kani::any();for x in input{kani::assume(x<2147483647);}let products:[u64;3]=kani::any();for x in products{kani::assume(x<=4611686009837453316);}let reply:u32=kani::any();kani::assume(reply<2147483647);let mut log=InterpolationLog{count:0,args:[[0;2];3],products,reductions:0,reduced:0,reply:M31(reply)};let out=NHU_interpolation_cut(input[0],input[1],input[2],input[3],input[4],input[5],&mut log);assert_eq!(out.0,reply^if cfg!(NHU_invert){1}else{0});assert_eq!(log.count,3);assert_eq!(log.reductions,1);assert_eq!(log.args,[[input[0],input[3]],[input[1],input[4]],[input[2],input[5]]]);assert_eq!(log.reduced,products[0]+products[1]+products[2]);}
