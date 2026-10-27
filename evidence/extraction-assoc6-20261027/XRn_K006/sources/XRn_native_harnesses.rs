use super::*;
use aspis_core::field::CM31;
// This counter records the whole NATIVE leaf's selected scalar call order.
// Only Dot push/finish arithmetic is stubbed. No verifier body is replaced.
static mut XRn_COUNT:usize=0;
static mut XRn_STOP:usize=174;
static mut XRn_HASHES:usize=0;
fn k(n:u32)->K {K{c0:CM31{a:M31(n),b:M31(0)},c1:CM31{a:M31(0),b:M31(0)}}}
#[derive(Clone,Copy)] struct Hash;
impl Digest32 for Hash {fn digest(&self,_:&[&[u8]])->[u8;32]{unsafe{XRn_HASHES+=1;} [0;32]}}
fn XRn_push(_: &mut crate::fast_pairing::EbyKDot,value:E,scalar:K)->Result<(),()> {
 let n=unsafe{XRn_COUNT}; assert!(n<174);assert_eq!(value,E::ZERO);
 assert_eq!(scalar,k((n+1) as u32));
 unsafe{XRn_COUNT=n+1;}
 if n==unsafe{XRn_STOP}{Err(())}else{Ok(())}
}
fn XRn_finish(_:crate::fast_pairing::EbyKDot)->E {E::ZERO}
fn sem()->crate::r1_semantic::Verified<Hash>{
 crate::r1_semantic::Verified{
 roots:[[0;32];2],challenges:crate::r1_wire::Challenges{lambda:K::ZERO,chi:K::ZERO,theta:K::ZERO,zc:[K::ZERO;10],mu:K::ZERO,eta:K::ZERO},
 alpha:[K::ZERO;10],claims:Box::new([[k(1),k(2),k(3),k(4),k(5),k(6),k(7),k(8),k(9),k(10),k(11),k(12),k(13),k(14),k(15),k(16),k(17),k(18),k(19),k(20),k(21),k(22),k(23),k(24),k(25),k(26),k(27),k(28),k(29)],[k(30),k(31),k(32),k(33),k(34),k(35),k(36),k(37),k(38),k(39),k(40),k(41),k(42),k(43),k(44),k(45),k(46),k(47),k(48),k(49),k(50),k(51),k(52),k(53),k(54),k(55),k(56),k(57),k(58)],[k(59),k(60),k(61),k(62),k(63),k(64),k(65),k(66),k(67),k(68),k(69),k(70),k(71),k(72),k(73),k(74),k(75),k(76),k(77),k(78),k(79),k(80),k(81),k(82),k(83),k(84),k(85),k(86),k(87)]]),extra:[k(88),k(89),k(90),k(91),k(92),k(93),k(94),k(95),k(96),k(97),k(98),k(99),k(100),k(101),k(102),k(103),k(104),k(105),k(106),k(107),k(108),k(109),k(110),k(111),k(112),k(113),k(114),k(115),k(116)],before_z1:[k(117),k(118),k(119),k(120),k(121),k(122),k(123),k(124),k(125),k(126),k(127),k(128),k(129),k(130),k(131),k(132),k(133),k(134),k(135),k(136),k(137),k(138),k(139),k(140),k(141),k(142),k(143),k(144),k(145)],state_before_z0:[0;32],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],
 transcript:crate::r1_wire::SemanticTranscript::new(Hash,&[],&[0;32]).unwrap()}
}
fn y1()->[u8;928]{
 let mut out=[0;928];
 for i in 0..29{let cell=E::from_qm31(k(146+i as u32)).to_le_bytes();out[32*i..32*(i+1)].copy_from_slice(&cell);}out
}
#[kani::proof] #[kani::unwind(176)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,XRn_push)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,XRn_finish)]
fn XRn_claim_selection_success(){
 unsafe{XRn_COUNT=0;XRn_STOP=174;XRn_HASHES=0;}
 let sem=sem();let y=y1();let out=prepared_claim(&sem,&y,E::ZERO,&[E::ZERO;29],E::ZERO);
 assert_eq!(out,Ok(E::ZERO));assert_eq!(unsafe{XRn_COUNT},174);assert_eq!(unsafe{XRn_HASHES},1);
}
#[kani::proof] #[kani::unwind(176)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,XRn_push)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,XRn_finish)]
fn XRn_claim_selection_error(){
 let stop:usize=kani::any();kani::assume(stop<174);
 unsafe{XRn_COUNT=0;XRn_STOP=stop;XRn_HASHES=0;}
 let sem=sem();let y=y1();let out=prepared_claim(&sem,&y,E::ZERO,&[E::ZERO;29],E::ZERO);
 assert_eq!(out,Err(Error::Parse));assert_eq!(unsafe{XRn_COUNT},stop+1);assert_eq!(unsafe{XRn_HASHES},1);
 kani::cover!(stop==0);kani::cover!(stop==173);
}
// After the whole-loop timeout, isolate the first actual rejected push.
fn XRn_powers<const N:usize>(_:E)->[E;N]{let mut out=[E::ZERO;N];if N>0{out[0]=E::ONE;}out}
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,XRn_push)]
#[kani::stub(crate::weights::powers,XRn_powers)]
fn XRn_claim_first_rejection(){
 unsafe{XRn_COUNT=0;XRn_STOP=0;XRn_HASHES=0;}
 let sem=sem();let out=prepared_claim(&sem,&[],E::ZERO,&[E::ZERO;29],E::ZERO);
 assert_eq!(out,Err(Error::Parse));assert_eq!(unsafe{XRn_COUNT},1);assert_eq!(unsafe{XRn_HASHES},1);
}

fn XRn_field(_: &[u8],i:usize)->E {assert_eq!(i,unsafe{XRn_COUNT}%29);E::from_qm31(k(146+i as u32))}

#[kani::proof] #[kani::unwind(32)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,XRn_push)]
#[kani::stub(crate::weights::powers,XRn_powers)]
fn XRn_claim_stop_28(){
 unsafe{XRn_COUNT=0;XRn_STOP=28;XRn_HASHES=0;}
 let sem=sem();let out=prepared_claim(&sem,&[],E::ZERO,&[E::ZERO;29],E::ZERO);
 assert_eq!(out,Err(Error::Parse));assert_eq!(unsafe{XRn_COUNT},29);assert_eq!(unsafe{XRn_HASHES},1);
}

#[kani::proof] #[kani::unwind(32)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,XRn_push)]
#[kani::stub(crate::weights::powers,XRn_powers)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,XRn_finish)]
fn XRn_claim_stop_29(){
 unsafe{XRn_COUNT=0;XRn_STOP=29;XRn_HASHES=0;}
 let sem=sem();let out=prepared_claim(&sem,&[],E::ZERO,&[E::ZERO;29],E::ZERO);
 assert_eq!(out,Err(Error::Parse));assert_eq!(unsafe{XRn_COUNT},30);assert_eq!(unsafe{XRn_HASHES},1);
}

#[kani::proof] #[kani::unwind(32)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,XRn_push)]
#[kani::stub(crate::weights::powers,XRn_powers)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,XRn_finish)]
fn XRn_claim_stop_58(){
 unsafe{XRn_COUNT=0;XRn_STOP=58;XRn_HASHES=0;}
 let sem=sem();let out=prepared_claim(&sem,&[],E::ZERO,&[E::ZERO;29],E::ZERO);
 assert_eq!(out,Err(Error::Parse));assert_eq!(unsafe{XRn_COUNT},59);assert_eq!(unsafe{XRn_HASHES},1);
}

#[kani::proof] #[kani::unwind(32)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,XRn_push)]
#[kani::stub(crate::weights::powers,XRn_powers)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,XRn_finish)]
fn XRn_claim_stop_87(){
 unsafe{XRn_COUNT=0;XRn_STOP=87;XRn_HASHES=0;}
 let sem=sem();let out=prepared_claim(&sem,&[],E::ZERO,&[E::ZERO;29],E::ZERO);
 assert_eq!(out,Err(Error::Parse));assert_eq!(unsafe{XRn_COUNT},88);assert_eq!(unsafe{XRn_HASHES},1);
}

#[kani::proof] #[kani::unwind(32)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,XRn_push)]
#[kani::stub(crate::weights::powers,XRn_powers)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,XRn_finish)]
fn XRn_claim_stop_116(){
 unsafe{XRn_COUNT=0;XRn_STOP=116;XRn_HASHES=0;}
 let sem=sem();let out=prepared_claim(&sem,&[],E::ZERO,&[E::ZERO;29],E::ZERO);
 assert_eq!(out,Err(Error::Parse));assert_eq!(unsafe{XRn_COUNT},117);assert_eq!(unsafe{XRn_HASHES},1);
}

#[kani::proof] #[kani::unwind(32)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,XRn_push)]
#[kani::stub(crate::weights::powers,XRn_powers)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,XRn_finish)]
#[kani::stub(crate::weights::field,XRn_field)]
fn XRn_claim_stop_145(){
 unsafe{XRn_COUNT=0;XRn_STOP=145;XRn_HASHES=0;}
 let sem=sem();let out=prepared_claim(&sem,&[],E::ZERO,&[E::ZERO;29],E::ZERO);
 assert_eq!(out,Err(Error::Parse));assert_eq!(unsafe{XRn_COUNT},146);assert_eq!(unsafe{XRn_HASHES},1);
}
