use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn NCA_header_control0(){let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();kani::assume(input[36]==1);out[36]=0;out[32..37].copy_from_slice(&input[32..37]);assert_eq!(out[36],0,"wrong unchanged byte for row0");}
fn NCA_header_control1(){let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();kani::assume(input[41]==1);out[41]=0;out[37..42].copy_from_slice(&input[37..42]);assert_eq!(out[41],0,"wrong unchanged byte for row1");}
fn NCA_header_control3(){let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();kani::assume(input[83]==1);out[83]=0;out[79..84].copy_from_slice(&input[79..84]);assert_eq!(out[83],0,"wrong unchanged byte for row3");}
fn NCA_header_control4(){let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();kani::assume(input[88]==1);out[88]=0;out[84..89].copy_from_slice(&input[84..89]);assert_eq!(out[88],0,"wrong unchanged byte for row4");}
fn NCA_header_control5(){let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();kani::assume(input[93]==1);out[93]=0;out[89..94].copy_from_slice(&input[89..94]);assert_eq!(out[93],0,"wrong unchanged byte for row5");}
fn NCA_header_control6(){let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();kani::assume(input[98]==1);out[98]=0;out[94..99].copy_from_slice(&input[94..99]);assert_eq!(out[98],0,"wrong unchanged byte for row6");}
fn NCA_header_control7(){let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();kani::assume(input[103]==1);out[103]=0;out[99..104].copy_from_slice(&input[99..104]);assert_eq!(out[103],0,"wrong unchanged byte for row7");}
fn NCA_header_control8(){let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();kani::assume(input[108]==1);out[108]=0;out[104..109].copy_from_slice(&input[104..109]);assert_eq!(out[108],0,"wrong unchanged byte for row8");}
fn NCA_header_control9(){let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();kani::assume(input[113]==1);out[113]=0;out[109..114].copy_from_slice(&input[109..114]);assert_eq!(out[113],0,"wrong unchanged byte for row9");}
fn NCA_header_control10(){let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();kani::assume(input[118]==1);out[118]=0;out[114..119].copy_from_slice(&input[114..119]);assert_eq!(out[118],0,"wrong unchanged byte for row10");}
fn NCA_header_control11(){let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();kani::assume(input[123]==1);out[123]=0;out[119..124].copy_from_slice(&input[119..124]);assert_eq!(out[123],0,"wrong unchanged byte for row11");}
fn NCA_header_control12(){let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();kani::assume(input[128]==1);out[128]=0;out[124..129].copy_from_slice(&input[124..129]);assert_eq!(out[128],0,"wrong unchanged byte for row12");}
fn NCA_header_control13(){let input:[u8;134]=kani::any();let mut out:[u8;134]=kani::any();kani::assume(input[133]==1);out[133]=0;out[129..134].copy_from_slice(&input[129..134]);assert_eq!(out[133],0,"wrong unchanged byte for row13");}
#[kani::proof]#[kani::unwind(7)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NCA_headers_strong_controls(){let row:usize=kani::any();kani::assume(row<13);match row{0=>NCA_header_control0(),1=>NCA_header_control1(),2=>NCA_header_control3(),3=>NCA_header_control4(),4=>NCA_header_control5(),5=>NCA_header_control6(),6=>NCA_header_control7(),7=>NCA_header_control8(),8=>NCA_header_control9(),9=>NCA_header_control10(),10=>NCA_header_control11(),11=>NCA_header_control12(),12=>NCA_header_control13(),_=>unreachable!()}}
