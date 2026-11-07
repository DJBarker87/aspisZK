import NNC_SourceCuts
set_option autoImplicit false
noncomputable section
namespace NNC_WeakOps
open Aeneas Aeneas.Std Result AspisR1
/-- Change only the actual TX2 verifier slot; no other native/model operation
or adversary program is changed. This is a local call-structure tool, not a
claim that the deployed dictionary has already been replaced or refined. -/
def replace (ops auth : AdapterRw.Ops) : AdapterRw.Ops := {ops with op11:=auth.op11}

theorem data (ops auth : AdapterRw.Ops) (a : AdapterRw.Cuts.Account) :
 AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (replace ops auth) a =
 AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops a := rfl

theorem readonly (ops auth : AdapterRw.Ops) (a : AdapterRw.Cuts.Account)
 (owner : AdapterRw.solana_pubkey.Pubkey) :
 AdapterRw.r1_pool_adapter.owned.require_readonly_account (replace ops auth) a owner =
 AdapterRw.r1_pool_adapter.owned.require_readonly_account ops a owner := rfl

theorem checkpoint (ops auth : AdapterRw.Ops) (a : AdapterRw.Cuts.Account)
 (owner : AdapterRw.solana_pubkey.Pubkey) (writable : Bool) :
 AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint (replace ops auth) a owner writable =
 AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint ops a owner writable := rfl

theorem distinctInnerBody (ops auth : AdapterRw.Ops) {N : Usize}
 (accounts : Array AdapterRw.Cuts.Account N) (i j : Usize) :
 AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body (replace ops auth) accounts i j =
 AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body ops accounts i j := rfl

theorem distinctInner (ops auth : AdapterRw.Ops) {N : Usize}
 (accounts : Array AdapterRw.Cuts.Account N) (i j : Usize) :
 AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0 (replace ops auth) accounts i j =
 AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0 ops accounts i j := by
 unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
 simp only [distinctInnerBody]

theorem distinctBody (ops auth : AdapterRw.Ops) {N : Usize}
 (accounts : Array AdapterRw.Cuts.Account N) (i : Usize) :
 AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0.body (replace ops auth) accounts i =
 AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0.body ops accounts i := by
 unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0.body
 simp only [distinctInner]

theorem distinctLoop (ops auth : AdapterRw.Ops) {N : Usize}
 (accounts : Array AdapterRw.Cuts.Account N) (i : Usize) :
 AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0 (replace ops auth) accounts i =
 AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0 ops accounts i := by
 unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0
 simp only [distinctBody]

theorem distinct (ops auth : AdapterRw.Ops) {N : Usize}
 (accounts : Array AdapterRw.Cuts.Account N) :
 AdapterRw.r1_pool_adapter.owned.require_distinct_accounts (replace ops auth) accounts =
 AdapterRw.r1_pool_adapter.owned.require_distinct_accounts ops accounts := by
 unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
 rw [distinctLoop]

theorem registry (ops auth : AdapterRw.Ops) (id pool : AdapterRw.solana_pubkey.Pubkey)
 (a : AdapterRw.Cuts.Account)
 (master : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg entry : AdapterRw.Cuts.Account) (slot : U64) :
 AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry (replace ops auth) id pool a master reg entry slot =
 AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry ops id pool a master reg entry slot := by
 unfold AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry
 simp only [readonly,data]
 rfl

theorem authentication (ops auth : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
 (accounts : S2W_ExtractionBoundary.Accounts) (pool : AdapterRw.solana_pubkey.Pubkey) (lane : U8) (slot : U64) :
 AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts (replace ops auth) id accounts pool lane slot =
 AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts ops id accounts pool lane slot := by
 unfold AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts
 simp only [readonly,checkpoint,distinct,registry,data]
 rfl

theorem validation (ops auth : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
 (accounts : S2W_ExtractionBoundary.Accounts) (input : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
 AdapterRw.r1_pool_adapter.owned.validate_asq8 (replace ops auth) id accounts input slot =
 AdapterRw.r1_pool_adapter.owned.validate_asq8 ops id accounts input slot := by
 unfold AdapterRw.r1_pool_adapter.owned.validate_asq8
 simp only [authentication,data]
 rfl

theorem encoding (ops auth : AdapterRw.Ops)
 (statement : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) :
 (replace ops auth).op22 statement=ops.op22 statement := rfl

#print axioms readonly
#print axioms checkpoint
#print axioms distinctInnerBody
#print axioms distinctInner
#print axioms distinctBody
#print axioms distinctLoop
#print axioms distinct
#print axioms registry
#print axioms authentication
#print axioms data
#print axioms validation
#print axioms encoding
end NNC_WeakOps
