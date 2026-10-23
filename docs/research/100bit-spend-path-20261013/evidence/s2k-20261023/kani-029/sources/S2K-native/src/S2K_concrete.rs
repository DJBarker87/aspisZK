// Width-32 specialization of S2G_copy; separately verified, not inherited
// from the width-1768 proof. Ghost observations preserve the original byte.
#[kani::requires(destination.len() == 32 && source.len() == 32)]
#[kani::requires(observed < 32)]
#[kani::requires(expected == source[observed])]
#[kani::modifies(destination.as_mut_ptr().cast::<[u8;32]>())]
#[kani::ensures(|_| destination[observed] == expected)]
pub fn S2K_copy32(destination: &mut [u8], source: &[u8], observed: usize, expected: u8) {
    destination.copy_from_slice(source);
}
#[kani::proof_for_contract(S2K_copy32)]
#[kani::unwind(34)]
fn S2K_copy32_contract() {
    let mut destination:[u8;32]=kani::any();
    let source:[u8;32]=kani::any();
    let observed:usize=kani::any(); kani::assume(observed<32);
    S2K_copy32(&mut destination,&source,observed,source[observed]);
    kani::cover!(observed==0); kani::cover!(observed==31);
}

// Source loop specialized at level=0; offsets 48..80.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_00() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<48 || i>=80);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[48..80],&source,j,expected);
    assert_eq!(output[48+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=1; offsets 80..112.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_01() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<80 || i>=112);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[80..112],&source,j,expected);
    assert_eq!(output[80+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=2; offsets 112..144.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_02() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<112 || i>=144);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[112..144],&source,j,expected);
    assert_eq!(output[112+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=3; offsets 144..176.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_03() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<144 || i>=176);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[144..176],&source,j,expected);
    assert_eq!(output[144+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=4; offsets 176..208.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_04() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<176 || i>=208);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[176..208],&source,j,expected);
    assert_eq!(output[176+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=5; offsets 208..240.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_05() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<208 || i>=240);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[208..240],&source,j,expected);
    assert_eq!(output[208+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=6; offsets 240..272.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_06() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<240 || i>=272);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[240..272],&source,j,expected);
    assert_eq!(output[240+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=7; offsets 272..304.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_07() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<272 || i>=304);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[272..304],&source,j,expected);
    assert_eq!(output[272+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=8; offsets 304..336.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_08() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<304 || i>=336);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[304..336],&source,j,expected);
    assert_eq!(output[304+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=9; offsets 336..368.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_09() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<336 || i>=368);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[336..368],&source,j,expected);
    assert_eq!(output[336+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=10; offsets 368..400.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_10() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<368 || i>=400);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[368..400],&source,j,expected);
    assert_eq!(output[368+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=11; offsets 400..432.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_11() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<400 || i>=432);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[400..432],&source,j,expected);
    assert_eq!(output[400+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=12; offsets 432..464.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_12() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<432 || i>=464);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[432..464],&source,j,expected);
    assert_eq!(output[432+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=13; offsets 464..496.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_13() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<464 || i>=496);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[464..496],&source,j,expected);
    assert_eq!(output[464+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=14; offsets 496..528.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_14() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<496 || i>=528);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[496..528],&source,j,expected);
    assert_eq!(output[496+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=15; offsets 528..560.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_15() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<528 || i>=560);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[528..560],&source,j,expected);
    assert_eq!(output[528+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=16; offsets 560..592.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_16() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<560 || i>=592);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[560..592],&source,j,expected);
    assert_eq!(output[560+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=17; offsets 592..624.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_17() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<592 || i>=624);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[592..624],&source,j,expected);
    assert_eq!(output[592+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=18; offsets 624..656.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_18() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<624 || i>=656);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[624..656],&source,j,expected);
    assert_eq!(output[624+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Source loop specialized at level=19; offsets 656..688.
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_frontier_level_19() {
    let mut output:[u8;688]=kani::any();
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<688);
    kani::assume(i<656 || i>=688);
    let before=output[i];
    let node=digest();
    let source=encode_digest_canonical(&node);
    let expected=source[j];
    S2K_copy32(&mut output[656..688],&source,j,expected);
    assert_eq!(output[656+j],(node[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0 && i==0); kani::cover!(j==31 && i==47);
}

// Actual iter().enumerate() shape over a frontier of exactly twenty rows.
// Row values are immaterial to the enumerator; the store is checked separately.
#[kani::proof]
#[kani::unwind(22)]
fn S2K_frontier_call_range() {
    let frontier:[Digest;20]=[ [M31(0);8];20 ];
    for (level, _node) in frontier.iter().enumerate() {
        assert!(level<20);
        assert!(48+32*level+32<=688);
    }
}
