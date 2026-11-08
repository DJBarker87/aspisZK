import NMX_R6_Args242
set_option autoImplicit false
namespace NMX_R6_AccountLeft
open Aeneas Aeneas.Std Result AdapterRw

theorem error (e : solana_program_error.ProgramError) :
 NMX_R2_ErrorInverse.fromError (NMX_R2_Carrier.error e) = e := by
 cases e <;> simp only [NMX_R2_Carrier.error,NMX_R2_ErrorInverse.fromError,
  NMX_R2_ErrorInverse.word_roundtrip]

theorem scalar (n : Usize) (h : n.val ≤ Usize.max) :
 NMX_R2_AccountReify.scalar n.val h = n := by
 apply UScalar.eq_of_val_eq
 exact NMX_R2_AccountReify.scalar_value _ _

theorem account (a : r1_pool_adapter.owned.OwnedAccount)
 (h : NMX_R2_AccountReify.Bounds (NMX_R2_Carrier.account a)) :
 NMX_R2_AccountReify.account (NMX_R2_Carrier.account a) h = a := by
 cases a with
 | mk key owner sign write exec length bytes =>
   cases length <;> cases bytes <;>
    simp only [NMX_R2_Carrier.account,NMX_R2_Carrier.reply,NMX_R2_AccountReify.account,
     NMX_R2_InverseBytes.array_roundtrip,error,scalar]
   all_goals congr 1
   all_goals first
   | apply congrArg core.result.Result.Ok
     apply Subtype.ext
     simp only [NMX_R2_Carrier.bytes,List.map_map,Function.comp_def,
      NMX_R2_InverseBytes.scalar_roundtrip,List.map_id]
     exact List.map_id _
   | rfl

#print axioms error
#print axioms scalar
#print axioms account
end NMX_R6_AccountLeft
