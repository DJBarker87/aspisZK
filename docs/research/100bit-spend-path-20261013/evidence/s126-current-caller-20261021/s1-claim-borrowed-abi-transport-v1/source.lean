import S1ClaimBorrowedAbiNativeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.BorrowedAbiTransport
open OwnedNestedTransfer
abbrev Q := aspis_core.field.QM31
abbrev Rows := Array (Array Q 29#usize) 3#usize
abbrev Row := Array Q 29#usize

theorem scalar_array {D : Type} {N : Usize} (ops : ClaimDotOps D)
    (claims : Rows) (extra before : Row) (bytes : Array U8 N) (point l : Usize) :
    verifier.borrowed_abi.owned_scalar ops claims extra before (Array.to_slice bytes) point l =
      verifier.owned_scalar ops claims extra before bytes point l := by
  simp only [verifier.borrowed_abi.owned_scalar,verifier.owned_scalar,lift,bind_tc_ok]
  rfl

theorem push_eq {D : Type} (ops : ClaimDotOps D) (dot : D)
    (g : Array E 29#usize) (l : Usize) (scalar : Q) :
    verifier.borrowed_abi.owned_push ops dot g l scalar = verifier.owned_push ops dot g l scalar := by rfl

theorem sum_eq (k parts : Parts) : verifier.borrowed_abi.owned_sum k parts=verifier.owned_sum k parts := by rfl

theorem inner_body_array {D : Type} {N : Usize} (ops : ClaimDotOps D)
    (claims : Rows) (extra before : Row) (bytes : Array U8 N)
    (g : Array E 29#usize) (point : Usize) (iter : Range) (dot : D) :
    verifier.borrowed_abi.owned_claim_loops_loop0_loop0.body ops claims extra before (Array.to_slice bytes) g point iter dot =
      verifier.owned_claim_loops_loop0_loop0.body ops claims extra before bytes g point iter dot := by
  unfold verifier.borrowed_abi.owned_claim_loops_loop0_loop0.body verifier.owned_claim_loops_loop0_loop0.body
  simp only [scalar_array,push_eq]

theorem inner_loop_array {D : Type} {N : Usize} (ops : ClaimDotOps D)
    (claims : Rows) (extra before : Row) (bytes : Array U8 N)
    (g : Array E 29#usize) (point : Usize) (iter : Range) (dot : D) :
    verifier.borrowed_abi.owned_claim_loops_loop0_loop0 ops iter claims extra before (Array.to_slice bytes) g point dot =
      verifier.owned_claim_loops_loop0_loop0 ops iter claims extra before bytes g point dot := by
  unfold verifier.borrowed_abi.owned_claim_loops_loop0_loop0 verifier.owned_claim_loops_loop0_loop0
  congr 1
  funext s
  rcases s with ⟨i,d⟩
  exact inner_body_array ops claims extra before bytes g point i d

theorem outer_body_array {D : Type} {N : Usize} (ops : ClaimDotOps D)
    (claims : Rows) (extra before : Row) (bytes : Array U8 N)
    (g : Array E 29#usize) (iter : Range) (parts : Parts) :
    verifier.borrowed_abi.owned_claim_loops_loop0.body ops claims extra before (Array.to_slice bytes) g iter parts =
      verifier.owned_claim_loops_loop0.body ops claims extra before bytes g iter parts := by
  unfold verifier.borrowed_abi.owned_claim_loops_loop0.body verifier.owned_claim_loops_loop0.body
  simp only [inner_loop_array]

theorem outer_loop_array {D : Type} {N : Usize} (ops : ClaimDotOps D)
    (claims : Rows) (extra before : Row) (bytes : Array U8 N)
    (g : Array E 29#usize) (iter : Range) (parts : Parts) :
    verifier.borrowed_abi.owned_claim_loops_loop0 ops iter claims extra before (Array.to_slice bytes) g parts =
      verifier.owned_claim_loops_loop0 ops iter claims extra before bytes g parts := by
  unfold verifier.borrowed_abi.owned_claim_loops_loop0 verifier.owned_claim_loops_loop0
  congr 1
  funext s
  rcases s with ⟨i,p⟩
  exact outer_body_array ops claims extra before bytes g i p

theorem claim_loops_array {D : Type} {N : Usize} (ops : ClaimDotOps D)
    (claims : Rows) (extra before : Row) (bytes : Array U8 N)
    (inactive kappa : E) (g : Array E 29#usize) :
    verifier.borrowed_abi.owned_claim_loops ops claims extra before (Array.to_slice bytes) inactive g kappa =
      verifier.owned_claim_loops ops claims extra before bytes inactive g kappa := by
  unfold verifier.borrowed_abi.owned_claim_loops verifier.owned_claim_loops
  simp only [outer_loop_array,sum_eq]

/-- Complete extracted reference on the ORIGINAL borrowed ABI, for ANY slice.
The array view is derived from that same slice; no byte-length, child-success
or canonicality premise is introduced. Native original/caller/P6 remains a
separate source-installation obligation. -/
theorem borrowed_claim_eq_source {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (bytes : Slice U8)
    (inactive kappa : E) (g : Array E 29#usize) :
    verifier.borrowed_abi.prepared_claim_owned ops inst sem bytes inactive g kappa =
      verifier.prepared_claim ops inst sem bytes inactive g kappa := by
  have h := claim_loops_array ops sem.claims sem.extra sem.before_z1
    (BorrowedAbiCarrier.asArray bytes) inactive kappa g
  rw [BorrowedAbiCarrier.same_slice] at h
  unfold verifier.borrowed_abi.prepared_claim_owned
  rw [h,OwnedNestedTransfer.owned_claim_eq ops inst sem (BorrowedAbiCarrier.asArray bytes) inactive kappa g,
    BorrowedAbiCarrier.same_slice]

#print axioms scalar_array
#print axioms push_eq
#print axioms sum_eq
#print axioms inner_body_array
#print axioms inner_loop_array
#print axioms outer_body_array
#print axioms outer_loop_array
#print axioms claim_loops_array
#print axioms borrowed_claim_eq_source
end AspisR1CurrentPreparedClaim.BorrowedAbiTransport
