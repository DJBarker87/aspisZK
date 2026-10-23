import S6FullForestCodecNativeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6FullForestCodec.Ranges
open aspis_statement.pool_v1.pair_forest_terminal
private theorem add_exact (a b c : Usize) (hc : c.val = a.val + b.val) :
    a + b = ok c := by
  obtain ⟨z, hz, hval⟩ := spec_imp_exists
    (Usize.add_spec (x := a) (y := b) (by scalar_tac))
  have he : z = c := by scalar_tac
  simpa only [he] using hz

/-- Only the finite source constant sum: 144 + (32 + 800 + (8 + 680)) + 216. -/
theorem statement_bytes : POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES = ok 1880#usize := by
  unfold POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES
    aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
    aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES
    aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
    aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
    aspis_statement.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
  have h1 : (32#usize : Usize) + 800#usize = ok 832#usize := add_exact _ _ _ (by scalar_tac)
  have h2 : (8#usize : Usize) + 680#usize = ok 688#usize := add_exact _ _ _ (by scalar_tac)
  have h3 : (832#usize : Usize) + 688#usize = ok 1520#usize := add_exact _ _ _ (by scalar_tac)
  have h4 : (144#usize : Usize) + 1520#usize = ok 1664#usize := add_exact _ _ _ (by scalar_tac)
  have h5 : (1664#usize : Usize) + 216#usize = ok 1880#usize := add_exact _ _ _ (by scalar_tac)
  simp only [h1, h2, h3, h4, h5, bind_tc_ok]


/-- Exact outer wrong-length error of the current boxed decoder, for arbitrary
children and arbitrary malformed bytes. No child or allocation call is reached. -/
theorem decode_wrong_length (ops : Ops) (bytes : Slice U8)
    (hn : bytes.val.length ≠ 1880) :
    decode ops bytes=ok (.Err PoolV1PairForestTerminalFormatErrorV1.WrongLength) := by
  have hlen : (Slice.len bytes).val=bytes.val.length := by
    simp only [Slice.len,Usize.ofNatCore_val_eq]
  have hne : Slice.len bytes ≠ 1880#usize := by
    intro h
    apply hn
    simpa only [← hlen] using congrArg (fun i : Usize => i.val) h
  have hb : (Slice.len bytes != 1880#usize)=true := by
    simpa only [bne_iff_ne] using hne
  unfold decode decode_pool_v1_pair_forest_terminal_statement_v1
  rw [statement_bytes,bind_tc_ok]
  simp only [hb,Bool.true_eq_true,if_true]

/-- Accepted-only range derived from the SAME actual outer decoder call. -/
theorem decode_success_length (ops : Ops) (bytes : Slice U8)
    (statement : PoolV1PairForestTerminalStatementV1)
    (h : decode ops bytes=ok (.Ok statement)) : bytes.val.length=1880 := by
  by_contra hn
  rw [decode_wrong_length ops bytes hn] at h
  cases h

#print axioms statement_bytes
#print axioms decode_wrong_length
#print axioms decode_success_length
end AspisS6FullForestCodec.Ranges
