import NCK_Distinct
import NCK_Owners
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_AuthenticationCuts
open Aeneas Aeneas.Std Result
open AdapterRw.Cuts
open _root_.AdapterRw.r1_pool_adapter.owned
attribute [local irreducible] require_readonly_buffer require_readonly_account
  require_verifier_checkpoint require_distinct_accounts OwnedAccount.data
  authenticate_invariant_release_registry

/-- Every guard below belongs to the SAME accepted authentication invocation.
Decoder/PDA/reconstruction results are not assumed successful independently. -/
theorem guards (ops : _root_.AdapterRw.Ops)
    (program pool : _root_.AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (lane : U8) (slot : U64)
    (authenticated : _root_.AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts)
    (success : authenticate_asq8_accounts ops program accounts pool lane slot = ok (.Ok authenticated)) :
    ∃ proof master poolCheckpoint laneAccount registry entry checkpoint,
      Slice.len accounts = 7#usize ∧
      Slice.index_usize accounts 0#usize = ok proof ∧
      Slice.index_usize accounts 1#usize = ok master ∧
      Slice.index_usize accounts 2#usize = ok poolCheckpoint ∧
      Slice.index_usize accounts 3#usize = ok laneAccount ∧
      Slice.index_usize accounts 4#usize = ok registry ∧
      Slice.index_usize accounts 5#usize = ok entry ∧
      Slice.index_usize accounts 6#usize = ok checkpoint ∧
      require_readonly_buffer proof = ok (.Ok ()) ∧
      require_verifier_checkpoint ops checkpoint program false = ok (.Ok ()) ∧
      require_readonly_account ops master pool = ok (.Ok ()) ∧
      require_readonly_account ops poolCheckpoint pool = ok (.Ok ()) ∧
      require_readonly_account ops laneAccount pool = ok (.Ok ()) ∧
      require_distinct_accounts ops (Array.make 7#usize
        [proof,master,poolCheckpoint,laneAccount,registry,entry,checkpoint]) = ok (.Ok ()) := by
  unfold authenticate_asq8_accounts at success
  change (if Slice.len accounts = 7#usize then _ else _) = _ at success
  by_cases arity : Slice.len accounts = 7#usize
  · rw [if_pos arity] at success
    obtain ⟨p,i0,success⟩ := bind_success _ _ _ success
    obtain ⟨m,i1,success⟩ := bind_success _ _ _ success
    obtain ⟨pc,i2,success⟩ := bind_success _ _ _ success
    obtain ⟨l,i3,success⟩ := bind_success _ _ _ success
    obtain ⟨reg,i4,success⟩ := bind_success _ _ _ success
    obtain ⟨en,i5,success⟩ := bind_success _ _ _ success
    obtain ⟨cp,i6,success⟩ := bind_success _ _ _ success
    obtain ⟨result0,g0,success⟩ := bind_success _ _ _ success
    cases result0 with
    | Err error =>
      try head_reduce success
      cases success
    | Ok value =>
      cases value
      try head_reduce success
      obtain ⟨result1,g1,success⟩ := bind_success _ _ _ success
      cases result1 with
      | Err error =>
        try head_reduce success
        cases success
      | Ok value =>
        cases value
        try head_reduce success
        obtain ⟨result2,g2,success⟩ := bind_success _ _ _ success
        cases result2 with
        | Err error =>
          try head_reduce success
          cases success
        | Ok value =>
          cases value
          try head_reduce success
          obtain ⟨result3,g3,success⟩ := bind_success _ _ _ success
          cases result3 with
          | Err error =>
            try head_reduce success
            cases success
          | Ok value =>
            cases value
            try head_reduce success
            obtain ⟨result4,g4,success⟩ := bind_success _ _ _ success
            cases result4 with
            | Err error =>
              try head_reduce success
              cases success
            | Ok value =>
              cases value
              try head_reduce success
              obtain ⟨result5,g5,success⟩ := bind_success _ _ _ success
              cases result5 with
              | Err error =>
                try head_reduce success
                cases success
              | Ok value =>
                cases value
                try head_reduce success
                exact ⟨p,m,pc,l,reg,en,cp,arity,i0,i1,i2,i3,i4,i5,i6,g0,g1,g2,g3,g4,g5⟩
  · rw [if_neg arity] at success
    by_cases short : Slice.len accounts < 7#usize
    · rw [if_pos short] at success
      cases success
    · rw [if_neg short] at success
      cases success
#print axioms guards
end AspisR1.NCK_AuthenticationCuts
end
