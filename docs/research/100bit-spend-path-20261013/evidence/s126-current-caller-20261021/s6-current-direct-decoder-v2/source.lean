import S6CurrentFirstInstallationV1
import S6CurrentCodecTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
noncomputable section
namespace AspisS6CurrentDirectDecoder
open AspisS6CurrentCodecInstallation AspisS6CurrentAdapterCarrier

/-- The complete original decoder, with only its nominal carrier transport
and the actual adapter's constant error mapping. No successful child or codec
law is an input. Allocation/runtime interpretation remains D188/Allocator. -/
def decode (bytes : Slice U8) : Result (core.result.Result Statement PE) :=
  AspisS6OuterNativeOps.resultMap
    (mapBoth fromPoolV1PairForestTerminalStatementV1 (fun _ => AdapterRw.solana_program_error.ProgramError.InvalidAccountData))
    (AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes)

/-- All Result branches, including outer fail/div and exact SDK rejection. -/
theorem decode_eq (bytes : Slice U8) :
    AspisS6CurrentCodecInstallation.decode bytes = decode bytes := by
  unfold AspisS6CurrentCodecInstallation.decode
  rw [boxed_eq]
  unfold boxOps rawDecoder decode
  cases run : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes with
  | fail e => rfl
  | div => rfl
  | ok reply => cases reply <;> rfl

/-- TOTAL at the extracted source interpretation; not native allocator/SDK
TOTAL. It reuses the original decoder's checked totality. -/
theorem decode_total (bytes : Slice U8) :
    ∃ reply, decode bytes = ok reply := by
  obtain ⟨reply, returned⟩ := AspisS6CurrentCodecInstallation.decode_total bytes
  exact ⟨reply, (decode_eq bytes).symm.trans returned⟩

/-- Exact same installed dictionary, stated with the original decoder directly
at the actual stage1 decoder slot. Other owners' slots are unchanged. -/
def install (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops) : AdapterRw.Ops :=
  {AspisS6CurrentFirstInstallation.install ops vops with op47 := decode}

theorem install_eq (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops) :
    install ops vops = AspisS6CurrentFirstInstallation.install ops vops := by
  have same : decode = AspisS6CurrentCodecInstallation.decode := by
    funext bytes
    exact (decode_eq bytes).symm
  unfold install
  rw [same]
  rfl

/-- Complete enclosing stage1 execution equality. No stage1/decoder success,
public canonicality, statement identity or independently chosen child is assumed.
All source errors and other SDK/stdlib operations retain the same dictionary. -/
theorem stage1_eq (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) :
    AdapterRw.r1_pool_adapter.owned.stage1_owned (AspisS6CurrentFirstInstallation.install ops vops)
      program accounts data =
    AdapterRw.r1_pool_adapter.owned.stage1_owned (install ops vops) program accounts data := by
  rw [install_eq]

/-- The original first_decoded caller has exactly the same complete computation
under the direct native-decoder source dictionary. -/
theorem first_decoded_eq (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops)
    (publicInput : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes proof : Slice U8) (split : Usize) :
    AdapterRw.first_decoded (install ops vops) publicInput bytes proof split =
      AdapterRw.first_decoded (AspisS6CurrentFirstInstallation.install ops vops) publicInput bytes proof split := by
  rw [install_eq]

#print axioms decode_eq
#print axioms decode_total
#print axioms install_eq
#print axioms stage1_eq
#print axioms first_decoded_eq
end AspisS6CurrentDirectDecoder
end
