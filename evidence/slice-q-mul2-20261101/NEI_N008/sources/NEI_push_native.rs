use aspis_core::field::{M31,QM31 as K};
fn residue_limb_at(row:&[u64;4],index:usize)->u64 {row[index]}
fn power_limb_at(limbs:&[u32;4],index:usize)->u32 {limbs[index]}
fn update_residue_row(row:&mut [u64;4],power:K,basis:M31,flush:bool) {
    let limbs=[power.c0.a.0,power.c0.b.0,power.c1.a.0,power.c1.b.0];
    for j in 0..4 {
        let old=residue_limb_at(row,j);
        let limb=power_limb_at(&limbs,j);
        row[j]=old+u64::from(limb)*u64::from(basis.0);
    }
    if flush {
        for limb in row {*limb=(*limb&0x7fff_ffff)+(*limb>>31);}
    }
}
fn k(words:[u32;4])->K{K{c0:aspis_core::field::CM31{a:M31(words[0]),b:M31(words[1])},c1:aspis_core::field::CM31{a:M31(words[2]),b:M31(words[3])}}}
struct BatchedWeights {raw:Vec<[u64;4]>,terms:usize}
impl BatchedWeights {fn push(&mut self,index:usize,power:K,basis:M31) {
        let flush=self.terms&3==3;
        update_residue_row(&mut self.raw[index],power,basis,flush);
    }}
fn expected(mut a:Vec<u64>)->Vec<u64>{if std::env::var("NEI_WRONG").is_ok(){a[0]^=1;}a}
#[test] fn NEI_push_differential(){
let mut b=BatchedWeights{raw:vec![[2147483648,2147483649,2147483650,2147483651],[2147483652,2147483653,2147483654,2147483655],[2147483656,2147483657,2147483658,2147483659]],terms:3};b.push(0,k([0,0,0,0]),M31(0));let mut got:Vec<u64>=b.raw.iter().flatten().copied().collect();got.push(b.terms as u64);assert_eq!(got,expected(vec![1,2,3,4,2147483652,2147483653,2147483654,2147483655,2147483656,2147483657,2147483658,2147483659,3]));
let mut b=BatchedWeights{raw:vec![[2147483648,2147483649,2147483650,2147483651],[2147483652,2147483653,2147483654,2147483655],[2147483656,2147483657,2147483658,2147483659]],terms:0};b.push(1,k([640585266,1401694993,590844326,1645146169]),M31(1330129639));let mut got:Vec<u64>=b.raw.iter().flatten().copied().collect();got.push(b.terms as u64);assert_eq!(got,expected(vec![2147483648,2147483649,2147483650,2147483651,852061450760782626,1864436057174681180,785899552195061968,2188257682021686646,2147483656,2147483657,2147483658,2147483659,0]));
let mut b=BatchedWeights{raw:vec![[2147483648,2147483649,2147483650,2147483651],[2147483652,2147483653,2147483654,2147483655],[2147483656,2147483657,2147483658,2147483659]],terms:1};b.push(2,k([684116573,1654619725,486239895,1644828829]),M31(583974315));let mut got:Vec<u64>=b.raw.iter().flatten().copied().collect();got.push(b.terms as u64);assert_eq!(got,expected(vec![2147483648,2147483649,2147483650,2147483651,2147483652,2147483653,2147483654,2147483655,399506509245306151,966255422639847032,283951611755780583,960537790855010794,1]));
let mut b=BatchedWeights{raw:vec![[2147483648,2147483649,2147483650,2147483651],[2147483652,2147483653,2147483654,2147483655],[2147483656,2147483657,2147483658,2147483659]],terms:2};b.push(0,k([1021504709,548257143,1580574866,564381121]),M31(668630530));let mut got:Vec<u64>=b.raw.iter().flatten().copied().collect();got.push(b.terms as u64);assert_eq!(got,expected(vec![683009237123649418,366581466247859439,1056820612505742630,377362450203707781,2147483652,2147483653,2147483654,2147483655,2147483656,2147483657,2147483658,2147483659,2]));
let mut b=BatchedWeights{raw:vec![[2147483648,2147483649,2147483650,2147483651],[2147483652,2147483653,2147483654,2147483655],[2147483656,2147483657,2147483658,2147483659]],terms:3};b.push(1,k([915903750,1814733430,1000707960,852600189]),M31(1283590606));let mut got:Vec<u64>=b.raw.iter().flatten().copied().collect();got.push(b.terms as u64);assert_eq!(got,expected(vec![2147483648,2147483649,2147483650,2147483651,1474598774,1385698566,2150237509,2271128240,2147483656,2147483657,2147483658,2147483659,3]));
let mut b=BatchedWeights{raw:vec![[2147483648,2147483649,2147483650,2147483651],[2147483652,2147483653,2147483654,2147483655],[2147483656,2147483657,2147483658,2147483659]],terms:7};b.push(2,k([1064571478,2004815668,1811781566,76271588]),M31(1023605638));let mut got:Vec<u64>=b.raw.iter().flatten().copied().collect();got.push(b.terms as u64);assert_eq!(got,expected(vec![2147483648,2147483649,2147483650,2147483651,2147483652,2147483653,2147483654,2147483655,1168553546,1539786573,1400509946,1811290516,7]));
let mut b=BatchedWeights{raw:vec![[0;4];64],terms:3};
b.push(23,k([1,2,3,4]),M31(5));let mut expected64=vec![[0;4];64];expected64[23]=[5,10,15,20];
if std::env::var("NEI_WRONG").is_ok(){expected64[0][0]^=1;}
assert_eq!(b.raw,expected64);assert_eq!(b.terms,3);
}
