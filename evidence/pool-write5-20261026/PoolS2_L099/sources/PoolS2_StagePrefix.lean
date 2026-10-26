import PoolS2_EntryMaster
import PoolS2_PrefixFacts
set_option autoImplicit false
namespace AspisR1.PoolS2_StagePrefix
open Aeneas Aeneas.Std Result S2W_D189Entry PoolS2_PdaSource

/-- One partial owned master stage supplies the source instruction and the
payer/System predicates of its SAME returned roles. Native caller not asserted. -/
theorem accepted (e : Entry) (decode : PoolS2_MasterRead.Decode) (pda : Ops)
    (program : Key) (data : Slice U8) (r : PoolS2_Prefix.Roles) (m : Master)
    (h : PoolS2_MasterStage.run decode pda program (PoolS2_RawSnapshot.accounts e) data = ok (.Ok (r,m))) :
    data.val = PoolS2_Instruction.wire ∧
    PoolS2_Payer.PayerOK r.payer ∧ PoolS2_Payer.SystemOK r.system := by
  have front := (PoolS2_MasterStage.accepted decode pda program _ data r m h).1
  have facts := PoolS2_PrefixFacts.accepted _ data r front
  exact ⟨facts.1,facts.2.2.2.2.1,facts.2.2.2.2.2⟩

#print axioms accepted
end AspisR1.PoolS2_StagePrefix
