import JHi_AuthenticationPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHi_AuthenticationRefusal
open Aeneas Aeneas.Std Result S2W_D189Wrappers
open _root_.AdapterRw

theorem source (base : Ops) (lane : U8) (slot : U64)
    (error : solana_program_error.ProgramError)
    (decoded : (JHd_KeyStd.install base).op48 JHg_DataMaster.value=ok (.Err error)) :
    r1_pool_adapter.owned.authenticate_asq8_accounts (JHd_KeyStd.install base)
      CPH_Program.verifier (JHg_World.e2.second secondSizes) JHb_Programs.pool lane slot=
      ok (.Err error) := by
  rw [JHi_AuthenticationPrefix.source]
  unfold JHi_Authentication.afterRead
  rw [decoded,bind_tc_ok]
#print axioms source

/-- Decoder association is necessary; an uninstalled callback may reject the
same retained bytes. This is not a counterexample to faithful native decoding. -/
theorem no_success (base : Ops) (lane : U8) (slot : U64)
    (error : solana_program_error.ProgramError)
    (decoded : (JHd_KeyStd.install base).op48 JHg_DataMaster.value=ok (.Err error)) :
    ¬∃ authenticated,r1_pool_adapter.owned.authenticate_asq8_accounts (JHd_KeyStd.install base)
      CPH_Program.verifier (JHg_World.e2.second secondSizes) JHb_Programs.pool lane slot=
      ok (.Ok authenticated) := by
  rintro ⟨authenticated,run⟩
  rw [source base lane slot error decoded] at run
  cases run
#print axioms no_success
end AspisR1.JHi_AuthenticationRefusal
end
