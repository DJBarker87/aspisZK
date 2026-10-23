import S6FiveCodecTypesV1
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisS6TransitionDiscriminantMeaning
open AspisS6FiveUnrolledCodec
abbrev Kind := aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind

theorem exact (kind : Kind) : (read_discriminant kind : U8)=
    (match kind with | .PrivateTransfer => 1#u8 | .Withdrawal => 2#u8) := by
  cases kind <;> rfl

#print axioms exact
end AspisS6TransitionDiscriminantMeaning
