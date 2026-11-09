import NOC_Op9
set_option autoImplicit false
open Lean Meta Elab Command
noncomputable section
namespace AspisR1.NOC_SlotAudit
open AspisR1.NNH_Run5bCtx
def cur {W Tx : Type} (c : Ctx W Tx) := DrvC_Installation.currentInstalled (configuration c)
def sdkC {W Tx : Type} (c : Ctx W Tx) := DrvC_Installation.sdk (configuration c)
end AspisR1.NOC_SlotAudit
end
namespace AspisR1.NOC_SlotAudit
/-- Diagnostic only: whnf of every slot applied to fresh variables, at the
host configuration, reporting the head constant (a residual m0 slot reduces
to `Aeneas.Std.Result.div`). -/
def audit (dictName structName : Name) (lo hi : Nat) : MetaM Unit := do
  withLocalDeclD `W (mkSort levelOne) fun W =>
  withLocalDeclD `Tx (mkSort levelOne) fun Tx =>
  withLocalDeclD `c (mkAppN (mkConst ``AspisR1.NNH_HostCtx.Ctx) #[W, Tx]) fun c => do
    let dict := mkAppN (mkConst dictName) #[W, Tx, c]
    let fields := getStructureFields (← getEnv) structName
    for i in [lo:min hi fields.size] do
      let f := fields[i]!
      let proj ← mkProjection dict f
      let msg ← forallTelescopeReducing (← inferType proj) fun xs _ => do
        let b ← whnf (mkAppN proj xs)
        let hd := b.getAppFn
        let shown ← if xs.size == 0 then pure (toString (← ppExpr b)) else pure ""
        pure s!"SLOT {structName}.{f} arity={xs.size} head={hd.constName?.getD `nonconst} {shown.take 200}"
      logInfo msg
end AspisR1.NOC_SlotAudit
run_meta AspisR1.NOC_SlotAudit.audit ``AspisR1.NOC_SlotAudit.cur ``AspisR1CurrentCaller.Ops 0 22
run_meta AspisR1.NOC_SlotAudit.audit ``AspisR1.NOC_SlotAudit.sdkC ``AdapterRw.Ops 0 15
run_meta AspisR1.NOC_SlotAudit.audit ``AspisR1.NOC_SlotAudit.sdkC ``AdapterRw.Ops 15 30
run_meta AspisR1.NOC_SlotAudit.audit ``AspisR1.NOC_SlotAudit.sdkC ``AdapterRw.Ops 30 45
run_meta AspisR1.NOC_SlotAudit.audit ``AspisR1.NOC_SlotAudit.sdkC ``AdapterRw.Ops 45 70
#print AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
#print AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len
#print AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0.body
#print AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body
#print AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
#print AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
#print AdapterRw.r1_pool_adapter.owned.first_decoded
#print AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
#print AdapterRw.solana_program_error.ProgramError.Insts.CoreCloneClone
#print AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey
