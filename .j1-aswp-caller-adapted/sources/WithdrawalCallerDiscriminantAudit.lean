import AspisR1WithdrawalCaller.Types
open Aeneas Aeneas.Std
namespace AspisR1WithdrawalCaller.DiscriminantAudit

theorem codes :
    read_discriminant (pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongLength) = 0#isize ∧
    read_discriminant (pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongMagic) = 1#isize ∧
    read_discriminant (pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongVersion) = 2#isize ∧
    read_discriminant (pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongTransitionKind) = 3#isize ∧
    read_discriminant (pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongDigestEncoding) = 4#isize ∧
    read_discriminant (pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonZeroReserved) = 5#isize ∧
    read_discriminant (pool_v1.payment_relation.PoolV1PaymentStatementFormatError.ZeroRequiredBinding) = 6#isize ∧
    read_discriminant (pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidAnchorSequence) = 7#isize ∧
    read_discriminant (pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest) = 8#isize ∧
    read_discriminant (pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalAssetId) = 9#isize ∧
    read_discriminant (pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidWithdrawalAmount) = 10#isize ∧
    read_discriminant (pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidDestination) = 11#isize ∧
    read_discriminant (pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidEnvelope) = 12#isize ∧
    read_discriminant (pool_v1.payment_relation.PoolV1PaymentStatementFormatError.EnvelopeMismatch) = 13#isize :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print pool_v1.payment_relation.PoolV1PaymentStatementFormatError.read_discriminant
#print axioms codes
end AspisR1WithdrawalCaller.DiscriminantAudit
