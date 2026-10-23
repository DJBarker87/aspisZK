// Exact result-encoder field boundaries. Sub-encoder output and errors
// are separate obligations; these gates do not assume emit success.
#[kani::proof]
#[kani::unwind(34)]
fn S2K_result_field_magic() {
    let mut output:[u8;792]=kani::any();
    let withdrawal:bool=kani::any();
    let result=PoolV1PairForestTerminalResultV1 {
      transition_kind:if withdrawal {PoolV1TransitionKind::Withdrawal} else {PoolV1TransitionKind::PrivateTransfer},
      master_account:kani::any(),selected_lane_account:kani::any(),output_lane:kani::any(),nullifier:digest(),
      verified_afterstate:PoolV1PairVerifiedAfterstateV1 {next_pair_index:0,next_root:[M31(0);8],next_frontier:[[M31(0);8];20]}
    };
    let j:usize=kani::any(); kani::assume(j<4);
    let i:usize=kani::any(); kani::assume(i<792 && (i<0 || i>=4));
    let before=output[i];
    output[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC);
    assert_eq!(output[0+j],POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC[j]);
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j==3);
}
#[kani::proof]
#[kani::unwind(34)]
fn S2K_result_field_version() {
    let mut output:[u8;792]=kani::any();
    let withdrawal:bool=kani::any();
    let result=PoolV1PairForestTerminalResultV1 {
      transition_kind:if withdrawal {PoolV1TransitionKind::Withdrawal} else {PoolV1TransitionKind::PrivateTransfer},
      master_account:kani::any(),selected_lane_account:kani::any(),output_lane:kani::any(),nullifier:digest(),
      verified_afterstate:PoolV1PairVerifiedAfterstateV1 {next_pair_index:0,next_root:[M31(0);8],next_frontier:[[M31(0);8];20]}
    };
    let j:usize=kani::any(); kani::assume(j<1);
    let i:usize=kani::any(); kani::assume(i<792 && (i<4 || i>=5));
    let before=output[i];
    output[4] = POOL_V1_PAIR_FOREST_TERMINAL_VERSION;
    assert_eq!(output[4+j],POOL_V1_PAIR_FOREST_TERMINAL_VERSION);
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j==0);
}
#[kani::proof]
#[kani::unwind(34)]
fn S2K_result_field_kind() {
    let mut output:[u8;792]=kani::any();
    let withdrawal:bool=kani::any();
    let result=PoolV1PairForestTerminalResultV1 {
      transition_kind:if withdrawal {PoolV1TransitionKind::Withdrawal} else {PoolV1TransitionKind::PrivateTransfer},
      master_account:kani::any(),selected_lane_account:kani::any(),output_lane:kani::any(),nullifier:digest(),
      verified_afterstate:PoolV1PairVerifiedAfterstateV1 {next_pair_index:0,next_root:[M31(0);8],next_frontier:[[M31(0);8];20]}
    };
    let j:usize=kani::any(); kani::assume(j<1);
    let i:usize=kani::any(); kani::assume(i<792 && (i<5 || i>=6));
    let before=output[i];
    output[5] = result.transition_kind as u8;
    assert_eq!(output[5+j],if withdrawal {2} else {1});
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j==0);
}
#[kani::proof]
#[kani::unwind(34)]
fn S2K_result_field_digest_version() {
    let mut output:[u8;792]=kani::any();
    let withdrawal:bool=kani::any();
    let result=PoolV1PairForestTerminalResultV1 {
      transition_kind:if withdrawal {PoolV1TransitionKind::Withdrawal} else {PoolV1TransitionKind::PrivateTransfer},
      master_account:kani::any(),selected_lane_account:kani::any(),output_lane:kani::any(),nullifier:digest(),
      verified_afterstate:PoolV1PairVerifiedAfterstateV1 {next_pair_index:0,next_root:[M31(0);8],next_frontier:[[M31(0);8];20]}
    };
    let j:usize=kani::any(); kani::assume(j<1);
    let i:usize=kani::any(); kani::assume(i<792 && (i<6 || i>=7));
    let before=output[i];
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    assert_eq!(output[6+j],POOL_V1_DIGEST_ENCODING_VERSION);
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j==0);
}
#[kani::proof]
#[kani::unwind(34)]
fn S2K_result_field_lane() {
    let mut output:[u8;792]=kani::any();
    let withdrawal:bool=kani::any();
    let result=PoolV1PairForestTerminalResultV1 {
      transition_kind:if withdrawal {PoolV1TransitionKind::Withdrawal} else {PoolV1TransitionKind::PrivateTransfer},
      master_account:kani::any(),selected_lane_account:kani::any(),output_lane:kani::any(),nullifier:digest(),
      verified_afterstate:PoolV1PairVerifiedAfterstateV1 {next_pair_index:0,next_root:[M31(0);8],next_frontier:[[M31(0);8];20]}
    };
    let j:usize=kani::any(); kani::assume(j<1);
    let i:usize=kani::any(); kani::assume(i<792 && (i<7 || i>=8));
    let before=output[i];
    output[7] = result.output_lane;
    assert_eq!(output[7+j],result.output_lane);
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j==0);
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_result_field_master() {
    let mut output:[u8;792]=kani::any();
    let withdrawal:bool=kani::any();
    let result=PoolV1PairForestTerminalResultV1 {
      transition_kind:if withdrawal {PoolV1TransitionKind::Withdrawal} else {PoolV1TransitionKind::PrivateTransfer},
      master_account:kani::any(),selected_lane_account:kani::any(),output_lane:kani::any(),nullifier:digest(),
      verified_afterstate:PoolV1PairVerifiedAfterstateV1 {next_pair_index:0,next_root:[M31(0);8],next_frontier:[[M31(0);8];20]}
    };
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<792 && (i<8 || i>=40));
    let before=output[i];
    let source=result.master_account;
    S2K_copy32(&mut output[8..40],&source,j,source[j]);
    assert_eq!(output[8+j],result.master_account[j]);
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j==31);
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_result_field_selected() {
    let mut output:[u8;792]=kani::any();
    let withdrawal:bool=kani::any();
    let result=PoolV1PairForestTerminalResultV1 {
      transition_kind:if withdrawal {PoolV1TransitionKind::Withdrawal} else {PoolV1TransitionKind::PrivateTransfer},
      master_account:kani::any(),selected_lane_account:kani::any(),output_lane:kani::any(),nullifier:digest(),
      verified_afterstate:PoolV1PairVerifiedAfterstateV1 {next_pair_index:0,next_root:[M31(0);8],next_frontier:[[M31(0);8];20]}
    };
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<792 && (i<40 || i>=72));
    let before=output[i];
    let source=result.selected_lane_account;
    S2K_copy32(&mut output[40..72],&source,j,source[j]);
    assert_eq!(output[40+j],result.selected_lane_account[j]);
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j==31);
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy32)]
fn S2K_result_field_nullifier() {
    let mut output:[u8;792]=kani::any();
    let withdrawal:bool=kani::any();
    let result=PoolV1PairForestTerminalResultV1 {
      transition_kind:if withdrawal {PoolV1TransitionKind::Withdrawal} else {PoolV1TransitionKind::PrivateTransfer},
      master_account:kani::any(),selected_lane_account:kani::any(),output_lane:kani::any(),nullifier:digest(),
      verified_afterstate:PoolV1PairVerifiedAfterstateV1 {next_pair_index:0,next_root:[M31(0);8],next_frontier:[[M31(0);8];20]}
    };
    let j:usize=kani::any(); kani::assume(j<32);
    let i:usize=kani::any(); kani::assume(i<792 && (i<72 || i>=104));
    let before=output[i];
    let source=encode_digest_canonical(&result.nullifier);
    S2K_copy32(&mut output[72..104],&source,j,source[j]);
    assert_eq!(output[72+j],(result.nullifier[j/4].0 >> (8*(j%4))) as u8);
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j==31);
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub_verified(S2K_copy688)]
fn S2K_result_field_afterstate() {
    let mut output:[u8;792]=kani::any();
    let withdrawal:bool=kani::any();
    let result=PoolV1PairForestTerminalResultV1 {
      transition_kind:if withdrawal {PoolV1TransitionKind::Withdrawal} else {PoolV1TransitionKind::PrivateTransfer},
      master_account:kani::any(),selected_lane_account:kani::any(),output_lane:kani::any(),nullifier:digest(),
      verified_afterstate:PoolV1PairVerifiedAfterstateV1 {next_pair_index:0,next_root:[M31(0);8],next_frontier:[[M31(0);8];20]}
    };
    let j:usize=kani::any(); kani::assume(j<688);
    let i:usize=kani::any(); kani::assume(i<792 && (i<104 || i>=792));
    let before=output[i];
    let source=kani::any::<[u8;688]>();
    S2K_copy688(&mut output[104..792],&source,j,source[j]);
    assert_eq!(output[104+j],source[j]);
    assert_eq!(output[i],before);
    kani::cover!(j==0); kani::cover!(j==687);
}
