// One windows(2) iteration and one iter().all membership predicate.
// Native predicate spellings are frozen well_formed source spans.
#[kani::proof]
fn wellformed_predicate_step(){let old:bool=kani::any();let pair:[u32;2]=kani::any();
 let mut windows=pair.windows(2);let w=windows.next().unwrap();let native=old && (w[0] < w[1]);
 let expected=old && pair[0]<pair[1];
 let i:u32=kani::any();let in_domain=i < 1 << LEAF_BITS;
 if cfg!(NDD_negative_wellformed){assert_ne!(native,expected);}else{assert_eq!(native,expected);assert_eq!(in_domain,i<262144);}
}
