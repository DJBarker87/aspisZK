import PoolS2_PrefixCuts
import PoolS2_PrefixUnique
set_option autoImplicit false
namespace AspisR1.PoolS2_PrefixFacts
open Aeneas Aeneas.Std Result PoolS2_Prefix PoolS2_PrefixSource

theorem accepted (accounts : Slice Account) (data : Slice U8) (roles : Roles)
    (h : run accounts data = ok (.Ok roles)) :
    data.val = PoolS2_Instruction.wire ∧ accounts.val.length = 12 ∧
    PoolS2_UniqueSuffix.allDifferent (keys accounts).val ∧
    select accounts = ok roles ∧ PoolS2_Payer.PayerOK roles.payer ∧ PoolS2_Payer.SystemOK roles.system := by
  obtain ⟨wire,count,unique,selected,payer⟩ := PoolS2_PrefixCuts.accepted accounts data roles h
  have full := PoolS2_Payer.accepted roles.payer roles.system payer
  exact ⟨(PoolS2_Instruction.accepted data).mp wire,
    (PoolS2_Count.accepted accounts 12#usize).mp count,
    (PoolS2_PrefixUnique.accepted accounts).mp unique,selected,full.1,full.2⟩

#print axioms accepted
end AspisR1.PoolS2_PrefixFacts
