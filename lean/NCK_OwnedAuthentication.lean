import NCK_ValidatedAuthCall
import NCK_AuthenticationDomains
import NCK_Stage2Shape
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_OwnedAuthentication
open Aeneas Aeneas.Std Result
open AdapterRw.Cuts
open _root_.AdapterRw.r1_pool_adapter.owned
/-- The authentication-domain theorem consumes a child derived from this
same whole accepted owned TX2. There is no independently existential run. -/
theorem source (ops : _root_.AdapterRw.Ops)
    (program : _root_.AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (slot : core.result.Result U64 PE)
    (success : stage2_owned ops program accounts data slot = ok (.Ok ())) :
    ∃ pool : _root_.AdapterRw.solana_pubkey.Pubkey, ∃ lane current authenticated,
      slot = .Ok current ∧
      authenticate_asq8_accounts ops program accounts pool lane current = ok (.Ok authenticated) := by
  obtain ⟨validated,_,_,_,_,_,_,_,_,auth,_,_,_,_,_,_,_,_,_⟩ :=
    AdapterRw.Cuts.stage2_call ops program accounts data slot success
  exact NCK_ValidatedAuthCall.source ops program accounts data slot validated auth
#print axioms source
end AspisR1.NCK_OwnedAuthentication
end
