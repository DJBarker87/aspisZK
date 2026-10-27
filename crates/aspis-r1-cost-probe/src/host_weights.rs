//! Prover-local fixed-storage weights (D187 batch 2).
use aspis_core::field::{QM31,QM31 as K,WideExact as E};
use aspis_core::circle::SecureCirclePoint;
use crate::{transport::Variant,verifier::Error};
pub use crate::weights::{QUARTER,PERM};
#[derive(Clone,Copy)]
pub struct Weights {pub variant:Variant,pub factors:[[[K;4];5];5],pub points:[[K;10];3],pub extra:[K;2]}
fn double(x:K)->K { x.mul(x).add(x.mul(x)).sub(K::ONE) }
fn state_only_statement_points(z: &[QM31; 10]) -> [[QM31; 10]; 3] {
    let mut successor = *z;
    let mut carry = QM31::ONE;
    let bit=z[9];let bit_and_carry=bit.mul(carry);successor[9]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[8];let bit_and_carry=bit.mul(carry);successor[8]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[7];let bit_and_carry=bit.mul(carry);successor[7]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[6];let bit_and_carry=bit.mul(carry);successor[6]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[5];let bit_and_carry=bit.mul(carry);successor[5]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[4];let bit_and_carry=bit.mul(carry);successor[4]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[3];let bit_and_carry=bit.mul(carry);successor[3]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[2];let bit_and_carry=bit.mul(carry);successor[2]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[1];let bit_and_carry=bit.mul(carry);successor[1]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let bit=z[0];let bit_and_carry=bit.mul(carry);successor[0]=bit.add(carry).sub(bit_and_carry.add(bit_and_carry));carry=bit_and_carry;
    let mut absorption = *z;
    absorption[7] = QM31::ONE.sub(absorption[7]);
    absorption[6] = QM31::ONE.sub(absorption[6]);
    [*z, successor, absorption]
}

impl Weights {
#[inline(never)]
pub fn new(variant:Variant,alpha:&[K;10],z:&[SecureCirclePoint;2])->Result<Weights,Error> {
        let points=state_only_statement_points(alpha);
        let extra=[alpha[8],alpha[9]];
        let mut factors=[[[K::ZERO;4];5];5];
    let a=points[0][3];let b=points[0][2];factors[0][0]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[0][1];let b=points[0][0];factors[0][1]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[0][5];let b=points[0][4];factors[0][2]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[0][9];let b=points[0][8];factors[0][3]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[0][7];let b=points[0][6];factors[0][4]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[1][3];let b=points[1][2];factors[1][0]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[1][1];let b=points[1][0];factors[1][1]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[1][5];let b=points[1][4];factors[1][2]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[1][9];let b=points[1][8];factors[1][3]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[1][7];let b=points[1][6];factors[1][4]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[2][3];let b=points[2][2];factors[2][0]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[2][1];let b=points[2][0];factors[2][1]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[2][5];let b=points[2][4];factors[2][2]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[2][9];let b=points[2][8];factors[2][3]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    let a=points[2][7];let b=points[2][6];factors[2][4]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];
    factors[3][0]=[K::ONE,z[0].y,z[0].x,z[0].x.mul(z[0].y)];let mut x=double(z[0].x);
    let y=double(x);factors[3][1]=[K::ONE,x,y,x.mul(y)];x=double(y);
    let y=double(x);factors[3][2]=[K::ONE,x,y,x.mul(y)];x=double(y);
    let y=double(x);factors[3][3]=[K::ONE,x,y,x.mul(y)];x=double(y);
    let y=double(x);factors[3][4]=[K::ONE,x,y,x.mul(y)];x=double(y);
    factors[4][0]=[K::ONE,z[1].y,z[1].x,z[1].x.mul(z[1].y)];let mut x=double(z[1].x);
    let y=double(x);factors[4][1]=[K::ONE,x,y,x.mul(y)];x=double(y);
    let y=double(x);factors[4][2]=[K::ONE,x,y,x.mul(y)];x=double(y);
    let y=double(x);factors[4][3]=[K::ONE,x,y,x.mul(y)];x=double(y);
    let y=double(x);factors[4][4]=[K::ONE,x,y,x.mul(y)];x=double(y);
        Ok(Weights {variant,factors,points,extra})
}
    pub fn raw(&self,kind:usize,j:usize)->K { raw_value(*self,kind,j) }

    /// The caller owns allocation and retains Error::Allocation before this kernel.
    pub fn materialize(&self,kappa:E,w:&mut [E;1024])->Result<(),Error> {
        let out=materialize_values(*self,kappa,*w);
        *w=out;
        Ok(())
    }
}

// The loop carries owned fixed arrays, with no loan from the caller at its joins.
type Powers7=(E,E,E,E,E,E,E);
// Array loans end inside this adapter; only value coordinates reach the loop.
fn powers7(x:E)->Powers7 {
    let p=crate::prover_powers::powers::<7>(x);
    (p[0],p[1],p[2],p[3],p[4],p[5],p[6])
}
fn materialize_cell(weights:Weights,k:Powers7,j:usize)->E {
    let mut v=E::ZERO;
    v=v.add(mul_qm31(k.0,raw_value(weights,0,j)));
    v=v.add(mul_qm31(k.1,raw_value(weights,1,j)));
    v=v.add(mul_qm31(k.2,raw_value(weights,2,j)));
    v=v.add(mul_qm31(k.3,raw_value(weights,3,j)));
    v=v.add(mul_qm31(k.4,raw_value(weights,4,j)));
    v=v.add(mul_qm31(k.5,raw_value(weights,5,j)));
    v=v.add(mul_qm31(k.6,raw_value(weights,6,j)));
    v
}
fn materialize_values(weights:Weights,kappa:E,mut out:[E;1024])->[E;1024] {
    let k=powers7(kappa);
    let mut j=0usize;
    while j<1024 {
        out[j]=materialize_cell(weights,k,j);
        j+=1;
    }
    out
}
// Literal form of the frozen COEFFICIENT_TO_ROW, avoiding its initializer's
// loan graph. D uses the same fixed-array indexing operation as Variant::row;
// in particular out-of-bounds inputs retain arrayOutOfBounds, not an assertion.
const HOST_COEFFICIENT_TO_ROW:[u16;1024]=[
    13,14,15,29,30,31,45,46,47,61,62,63,77,78,79,93,94,95,109,110,111,125,126,127,141,142,143,157,158,159,173,174,
    175,189,190,191,205,206,207,221,222,223,237,238,239,253,254,255,269,270,271,285,286,287,301,302,303,317,318,319,333,334,335,349,
    350,351,365,366,367,381,382,383,397,398,399,413,414,415,429,430,431,445,446,447,461,462,463,477,478,0,1,2,3,4,5,6,
    7,8,9,10,11,12,16,17,18,19,20,21,22,23,24,25,26,27,28,32,33,34,35,36,37,38,39,40,41,42,43,44,
    48,49,50,51,52,53,54,55,56,57,58,59,60,64,65,66,67,68,69,70,71,72,73,74,75,76,80,81,82,83,84,85,
    86,87,88,89,90,91,92,96,97,98,99,100,101,102,103,104,105,106,107,108,112,113,114,115,116,117,118,119,120,121,122,123,
    124,128,129,130,131,132,133,134,135,136,137,138,139,140,144,145,146,147,148,149,150,151,152,153,154,155,156,160,161,162,163,164,
    165,166,167,168,169,170,171,172,176,177,178,179,180,181,182,183,184,185,186,187,188,192,193,194,195,196,197,198,199,200,201,202,
    203,204,208,209,210,211,212,213,214,215,216,217,218,219,220,224,225,226,227,228,229,230,231,232,233,234,235,236,240,241,242,243,
    244,245,246,247,248,249,250,251,252,256,257,258,259,260,261,262,263,264,265,266,267,268,272,273,274,275,276,277,278,279,280,281,
    282,283,284,288,289,290,291,292,293,294,295,296,297,298,299,300,304,305,306,307,308,309,310,311,312,313,314,315,316,320,321,322,
    323,324,325,326,327,328,329,330,331,332,336,337,338,339,340,341,342,343,344,345,346,347,348,352,353,354,355,356,357,358,359,360,
    361,362,363,364,368,369,370,371,372,373,374,375,376,377,378,379,380,384,385,386,387,388,389,390,391,392,393,394,395,396,400,401,
    402,403,404,405,406,407,408,409,410,411,412,416,417,418,419,420,421,422,423,424,425,426,427,428,432,433,434,435,436,437,438,439,
    440,441,442,443,444,448,449,450,451,452,453,454,455,456,457,458,459,460,464,465,466,467,468,469,470,471,472,473,474,475,476,479,
    480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,
    512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,
    544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,
    576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,
    608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,
    640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,
    672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,
    704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,
    736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,
    768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,
    800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,
    832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,
    864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,
    896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,
    928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,
    960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991,
    992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,1023,
];
fn host_row(variant:Variant,j:usize)->usize {
    if let Variant::D=variant {
        return HOST_COEFFICIENT_TO_ROW[j] as usize;
    }
    let mut out=0usize;
    let mut d=0usize;
    while d<5 {
        out|=((j>>((2*d) as u32))&3) << ((2*crate::transport::TAU[d]) as u32);
        d+=1;
    }
    out
}
fn raw_value(weights:Weights,kind:usize,j:usize)->K {
        if kind==0 {
            let r=host_row(weights.variant,j);
            return if (aspis_core::r0::opening::COPY_ACTIVE_ROW_MASKS[r/16]>>(r%16))&1==0 {K::ONE}else{K::ZERO};
        }
        if kind==4 {
            if j<56 { return weights.extra[j/28].pow((j%28) as u64); }
            return K::ZERO;
        }
        if kind>=1 && kind<=3 && weights.variant==Variant::D {
            let r=host_row(weights.variant,j);
            return point_raw(weights.points[kind-1],r);
        }
        let k=if kind<4 {kind-1}else{kind-2};
        tensor_raw(weights.factors[k],j)
}

// Copy values before branch joins: no mutable element loan or restoration.
fn point_factor(point:K,r:usize,b:u32)->K {
    if r&(1usize<<b)==0 {K::ONE.sub(point)}else{point}
}
fn point_raw(points:[K;10],r:usize)->K {
    let mut v=K::ONE;
    v=v.mul(point_factor(points[9],r,0));
    v=v.mul(point_factor(points[8],r,1));
    v=v.mul(point_factor(points[7],r,2));
    v=v.mul(point_factor(points[6],r,3));
    v=v.mul(point_factor(points[5],r,4));
    v=v.mul(point_factor(points[4],r,5));
    v=v.mul(point_factor(points[3],r,6));
    v=v.mul(point_factor(points[2],r,7));
    v=v.mul(point_factor(points[1],r,8));
    v=v.mul(point_factor(points[0],r,9));
    v
}
fn tensor_raw(factors:[[K;4];5],j:usize)->K {
    let mut v=K::ONE;
    v=v.mul(factors[0][(j>>0u32)&3]);
    v=v.mul(factors[1][(j>>2u32)&3]);
    v=v.mul(factors[2][(j>>4u32)&3]);
    v=v.mul(factors[3][(j>>6u32)&3]);
    v=v.mul(factors[4][(j>>8u32)&3]);
    v
}
// Avoid canonical_qm31's FnOnce closure Drop in the extraction closure.
// The four reductions are exactly the shipped canonicalization of raw K.
fn mul_qm31(x:E,rhs:K)->E {
    use aspis_core::field::{CM31,M31,ct};
    let rhs=K {
        c0:CM31 {a:M31(ct::reduce64(rhs.c0.a.0 as u64)),b:M31(ct::reduce64(rhs.c0.b.0 as u64))},
        c1:CM31 {a:M31(ct::reduce64(rhs.c1.a.0 as u64)),b:M31(ct::reduce64(rhs.c1.b.0 as u64))},
    };
    let a=x.c0().mul(rhs);
    let b=x.c1().mul(rhs);
    E::from_limbs([a.c0.a.0,a.c0.b.0,a.c1.a.0,a.c1.b.0,
                   b.c0.a.0,b.c0.b.0,b.c1.a.0,b.c1.b.0]).unwrap()
}
