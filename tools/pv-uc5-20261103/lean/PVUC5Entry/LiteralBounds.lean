import Aeneas
import PV_UC5_LiteralBounds
open Aeneas Aeneas.Std
namespace PV_UC5_Literals
theorem size_0 : "lane_leaf_sets".toByteArray.size = 14 := by
  change (String.ofList ['l', 'a', 'n', 'e', '_', 'l', 'e', 'a', 'f', '_', 's', 'e', 't', 's']).toByteArray.size = 14
  rfl
theorem bound_0 : "lane_leaf_sets".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_0 (by omega)
#print axioms size_0
#print axioms bound_0
theorem size_1 : "11111111111111111111111111111111".toByteArray.size = 32 := by
  change (String.ofList ['1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1', '1']).toByteArray.size = 32
  rfl
theorem bound_1 : "11111111111111111111111111111111".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_1 (by omega)
#print axioms size_1
#print axioms bound_1
theorem size_2 : "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA".toByteArray.size = 43 := by
  change (String.ofList ['T', 'o', 'k', 'e', 'n', 'k', 'e', 'g', 'Q', 'f', 'e', 'Z', 'y', 'i', 'N', 'w', 'A', 'J', 'b', 'N', 'b', 'G', 'K', 'P', 'F', 'X', 'C', 'W', 'u', 'B', 'v', 'f', '9', 'S', 's', '6', '2', '3', 'V', 'Q', '5', 'D', 'A']).toByteArray.size = 43
  rfl
theorem bound_2 : "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_2 (by omega)
#print axioms size_2
#print axioms bound_2
theorem size_3 : "program".toByteArray.size = 7 := by
  change (String.ofList ['p', 'r', 'o', 'g', 'r', 'a', 'm']).toByteArray.size = 7
  rfl
theorem bound_3 : "program".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_3 (by omega)
#print axioms size_3
#print axioms bound_3
theorem size_4 : "accounts".toByteArray.size = 8 := by
  change (String.ofList ['a', 'c', 'c', 'o', 'u', 'n', 't', 's']).toByteArray.size = 8
  rfl
theorem bound_4 : "accounts".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_4 (by omega)
#print axioms size_4
#print axioms bound_4
theorem size_5 : "data".toByteArray.size = 4 := by
  change (String.ofList ['d', 'a', 't', 'a']).toByteArray.size = 4
  rfl
theorem bound_5 : "data".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_5 (by omega)
#print axioms size_5
#print axioms bound_5
theorem size_6 : "wallet_bytes_fd".toByteArray.size = 15 := by
  change (String.ofList ['w', 'a', 'l', 'l', 'e', 't', '_', 'b', 'y', 't', 'e', 's', '_', 'f', 'd']).toByteArray.size = 15
  rfl
theorem bound_6 : "wallet_bytes_fd".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_6 (by omega)
#print axioms size_6
#print axioms bound_6
theorem size_7 : "lane_bytes".toByteArray.size = 10 := by
  change (String.ofList ['l', 'a', 'n', 'e', '_', 'b', 'y', 't', 'e', 's']).toByteArray.size = 10
  rfl
theorem bound_7 : "lane_bytes".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_7 (by omega)
#print axioms size_7
#print axioms bound_7
theorem size_8 : "checkpoint_bytes".toByteArray.size = 16 := by
  change (String.ofList ['c', 'h', 'e', 'c', 'k', 'p', 'o', 'i', 'n', 't', '_', 'b', 'y', 't', 'e', 's']).toByteArray.size = 16
  rfl
theorem bound_8 : "checkpoint_bytes".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_8 (by omega)
#print axioms size_8
#print axioms bound_8
theorem size_9 : "withdrawal".toByteArray.size = 10 := by
  change (String.ofList ['w', 'i', 't', 'h', 'd', 'r', 'a', 'w', 'a', 'l']).toByteArray.size = 10
  rfl
theorem bound_9 : "withdrawal".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_9 (by omega)
#print axioms size_9
#print axioms bound_9
theorem size_10 : "withdrawal_amount".toByteArray.size = 17 := by
  change (String.ofList ['w', 'i', 't', 'h', 'd', 'r', 'a', 'w', 'a', 'l', '_', 'a', 'm', 'o', 'u', 'n', 't']).toByteArray.size = 17
  rfl
theorem bound_10 : "withdrawal_amount".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_10 (by omega)
#print axioms size_10
#print axioms bound_10
theorem size_11 : "destination".toByteArray.size = 11 := by
  change (String.ofList ['d', 'e', 's', 't', 'i', 'n', 'a', 't', 'i', 'o', 'n']).toByteArray.size = 11
  rfl
theorem bound_11 : "destination".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_11 (by omega)
#print axioms size_11
#print axioms bound_11
theorem size_12 : "checkpoint".toByteArray.size = 10 := by
  change (String.ofList ['c', 'h', 'e', 'c', 'k', 'p', 'o', 'i', 'n', 't']).toByteArray.size = 10
  rfl
theorem bound_12 : "checkpoint".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_12 (by omega)
#print axioms size_12
#print axioms bound_12
theorem size_13 : "proof_dir".toByteArray.size = 9 := by
  change (String.ofList ['p', 'r', 'o', 'o', 'f', '_', 'd', 'i', 'r']).toByteArray.size = 9
  rfl
theorem bound_13 : "proof_dir".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_13 (by omega)
#print axioms size_13
#print axioms bound_13
theorem size_14 : "mask-nonce-ledger".toByteArray.size = 17 := by
  change (String.ofList ['m', 'a', 's', 'k', '-', 'n', 'o', 'n', 'c', 'e', '-', 'l', 'e', 'd', 'g', 'e', 'r']).toByteArray.size = 17
  rfl
theorem bound_14 : "mask-nonce-ledger".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_14 (by omega)
#print axioms size_14
#print axioms bound_14
theorem size_15 : "proof.bin".toByteArray.size = 9 := by
  change (String.ofList ['p', 'r', 'o', 'o', 'f', '.', 'b', 'i', 'n']).toByteArray.size = 9
  rfl
theorem bound_15 : "proof.bin".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_15 (by omega)
#print axioms size_15
#print axioms bound_15
theorem size_16 : "statement.bin".toByteArray.size = 13 := by
  change (String.ofList ['s', 't', 'a', 't', 'e', 'm', 'e', 'n', 't', '.', 'b', 'i', 'n']).toByteArray.size = 13
  rfl
theorem bound_16 : "statement.bin".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_16 (by omega)
#print axioms size_16
#print axioms bound_16
theorem size_17 : "payer".toByteArray.size = 5 := by
  change (String.ofList ['p', 'a', 'y', 'e', 'r']).toByteArray.size = 5
  rfl
theorem bound_17 : "payer".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_17 (by omega)
#print axioms size_17
#print axioms bound_17
theorem size_18 : "verifier".toByteArray.size = 8 := by
  change (String.ofList ['v', 'e', 'r', 'i', 'f', 'i', 'e', 'r']).toByteArray.size = 8
  rfl
theorem bound_18 : "verifier".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_18 (by omega)
#print axioms size_18
#print axioms bound_18
theorem size_19 : "public_account".toByteArray.size = 14 := by
  change (String.ofList ['p', 'u', 'b', 'l', 'i', 'c', '_', 'a', 'c', 'c', 'o', 'u', 'n', 't']).toByteArray.size = 14
  rfl
theorem bound_19 : "public_account".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_19 (by omega)
#print axioms size_19
#print axioms bound_19
theorem size_20 : "verifier_checkpoint".toByteArray.size = 19 := by
  change (String.ofList ['v', 'e', 'r', 'i', 'f', 'i', 'e', 'r', '_', 'c', 'h', 'e', 'c', 'k', 'p', 'o', 'i', 'n', 't']).toByteArray.size = 19
  rfl
theorem bound_20 : "verifier_checkpoint".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_20 (by omega)
#print axioms size_20
#print axioms bound_20
theorem size_21 : "mint".toByteArray.size = 4 := by
  change (String.ofList ['m', 'i', 'n', 't']).toByteArray.size = 4
  rfl
theorem bound_21 : "mint".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_21 (by omega)
#print axioms size_21
#print axioms bound_21
theorem size_22 : "client_route".toByteArray.size = 12 := by
  change (String.ofList ['c', 'l', 'i', 'e', 'n', 't', '_', 'r', 'o', 'u', 't', 'e']).toByteArray.size = 12
  rfl
theorem bound_22 : "client_route".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_22 (by omega)
#print axioms size_22
#print axioms bound_22
theorem size_23 : "selected64-proof-account-v1".toByteArray.size = 27 := by
  change (String.ofList ['s', 'e', 'l', 'e', 'c', 't', 'e', 'd', '6', '4', '-', 'p', 'r', 'o', 'o', 'f', '-', 'a', 'c', 'c', 'o', 'u', 'n', 't', '-', 'v', '1']).toByteArray.size = 27
  rfl
theorem bound_23 : "selected64-proof-account-v1".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_23 (by omega)
#print axioms size_23
#print axioms bound_23
theorem size_24 : "proof_account".toByteArray.size = 13 := by
  change (String.ofList ['p', 'r', 'o', 'o', 'f', '_', 'a', 'c', 'c', 'o', 'u', 'n', 't']).toByteArray.size = 13
  rfl
theorem bound_24 : "proof_account".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_24 (by omega)
#print axioms size_24
#print axioms bound_24
theorem size_25 : "attempt_index".toByteArray.size = 13 := by
  change (String.ofList ['a', 't', 't', 'e', 'm', 'p', 't', '_', 'i', 'n', 'd', 'e', 'x']).toByteArray.size = 13
  rfl
theorem bound_25 : "attempt_index".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_25 (by omega)
#print axioms size_25
#print axioms bound_25
theorem size_26 : "prove_wall_seconds".toByteArray.size = 18 := by
  change (String.ofList ['p', 'r', 'o', 'v', 'e', '_', 'w', 'a', 'l', 'l', '_', 's', 'e', 'c', 'o', 'n', 'd', 's']).toByteArray.size = 18
  rfl
theorem bound_26 : "prove_wall_seconds".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_26 (by omega)
#print axioms size_26
#print axioms bound_26
theorem size_27 : "attempts".toByteArray.size = 8 := by
  change (String.ofList ['a', 't', 't', 'e', 'm', 'p', 't', 's']).toByteArray.size = 8
  rfl
theorem bound_27 : "attempts".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_27 (by omega)
#print axioms size_27
#print axioms bound_27
theorem size_28 : "p_r1".toByteArray.size = 4 := by
  change (String.ofList ['p', '_', 'r', '1']).toByteArray.size = 4
  rfl
theorem bound_28 : "p_r1".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_28 (by omega)
#print axioms size_28
#print axioms bound_28
theorem size_29 : "proof_bytes".toByteArray.size = 11 := by
  change (String.ofList ['p', 'r', 'o', 'o', 'f', '_', 'b', 'y', 't', 'e', 's']).toByteArray.size = 11
  rfl
theorem bound_29 : "proof_bytes".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_29 (by omega)
#print axioms size_29
#print axioms bound_29
theorem size_30 : "proof_upload_count".toByteArray.size = 18 := by
  change (String.ofList ['p', 'r', 'o', 'o', 'f', '_', 'u', 'p', 'l', 'o', 'a', 'd', '_', 'c', 'o', 'u', 'n', 't']).toByteArray.size = 18
  rfl
theorem bound_30 : "proof_upload_count".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_30 (by omega)
#print axioms size_30
#print axioms bound_30
theorem size_31 : "statement_upload_count".toByteArray.size = 22 := by
  change (String.ofList ['s', 't', 'a', 't', 'e', 'm', 'e', 'n', 't', '_', 'u', 'p', 'l', 'o', 'a', 'd', '_', 'c', 'o', 'u', 'n', 't']).toByteArray.size = 22
  rfl
theorem bound_31 : "statement_upload_count".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_31 (by omega)
#print axioms size_31
#print axioms bound_31
theorem size_32 : "marker".toByteArray.size = 6 := by
  change (String.ofList ['m', 'a', 'r', 'k', 'e', 'r']).toByteArray.size = 6
  rfl
theorem bound_32 : "marker".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_32 (by omega)
#print axioms size_32
#print axioms bound_32
theorem size_33 : "output_lane".toByteArray.size = 11 := by
  change (String.ofList ['o', 'u', 't', 'p', 'u', 't', '_', 'l', 'a', 'n', 'e']).toByteArray.size = 11
  rfl
theorem bound_33 : "output_lane".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_33 (by omega)
#print axioms size_33
#print axioms bound_33
theorem size_34 : "page".toByteArray.size = 4 := by
  change (String.ofList ['p', 'a', 'g', 'e']).toByteArray.size = 4
  rfl
theorem bound_34 : "page".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_34 (by omega)
#print axioms size_34
#print axioms bound_34
theorem size_35 : "needs_zero_page".toByteArray.size = 15 := by
  change (String.ofList ['n', 'e', 'e', 'd', 's', '_', 'z', 'e', 'r', 'o', '_', 'p', 'a', 'g', 'e']).toByteArray.size = 15
  rfl
theorem bound_35 : "needs_zero_page".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_35 (by omega)
#print axioms size_35
#print axioms bound_35
theorem size_36 : "settle".toByteArray.size = 6 := by
  change (String.ofList ['s', 'e', 't', 't', 'l', 'e']).toByteArray.size = 6
  rfl
theorem bound_36 : "settle".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_36 (by omega)
#print axioms size_36
#print axioms bound_36
theorem size_37 : "stage1".toByteArray.size = 6 := by
  change (String.ofList ['s', 't', 'a', 'g', 'e', '1']).toByteArray.size = 6
  rfl
theorem bound_37 : "stage1".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_37 (by omega)
#print axioms size_37
#print axioms bound_37
theorem size_38 : "action".toByteArray.size = 6 := by
  change (String.ofList ['a', 'c', 't', 'i', 'o', 'n']).toByteArray.size = 6
  rfl
theorem bound_38 : "action".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_38 (by omega)
#print axioms size_38
#print axioms bound_38
theorem size_39 : "prove".toByteArray.size = 5 := by
  change (String.ofList ['p', 'r', 'o', 'v', 'e']).toByteArray.size = 5
  rfl
theorem bound_39 : "prove".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_39 (by omega)
#print axioms size_39
#print axioms bound_39
theorem size_40 : "pool".toByteArray.size = 4 := by
  change (String.ofList ['p', 'o', 'o', 'l']).toByteArray.size = 4
  rfl
theorem bound_40 : "pool".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_40 (by omega)
#print axioms size_40
#print axioms bound_40
theorem size_41 : "registry".toByteArray.size = 8 := by
  change (String.ofList ['r', 'e', 'g', 'i', 's', 't', 'r', 'y']).toByteArray.size = 8
  rfl
theorem bound_41 : "registry".toByteArray.size ≤ U32.max :=
  PV_UC5_LiteralBounds.short_bound _ _ size_41 (by omega)
#print axioms size_41
#print axioms bound_41
end PV_UC5_Literals
