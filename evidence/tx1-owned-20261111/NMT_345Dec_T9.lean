import NMT_345Dec_T8
import NFY_Part058
set_option autoImplicit false
noncomputable section
namespace NMT_345Dec
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT9 : NMT_stage1_owned.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError → AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
 | .WrongLength => .WrongLength
 | .WrongMagic => .WrongMagic
 | .WrongVersion => .WrongVersion
 | .WrongTransitionKind => .WrongTransitionKind
 | .WrongDigestEncoding => .WrongDigestEncoding
 | .NonZeroReserved => .NonZeroReserved
 | .ZeroRequiredBinding => .ZeroRequiredBinding
 | .InvalidAnchorSequence => .InvalidAnchorSequence
 | .NonCanonicalDigest => .NonCanonicalDigest
 | .NonCanonicalAssetId => .NonCanonicalAssetId
 | .InvalidWithdrawalAmount => .InvalidWithdrawalAmount
 | .InvalidDestination => .InvalidDestination
 | .InvalidEnvelope => .InvalidEnvelope
 | .EnvelopeMismatch => .EnvelopeMismatch
def fromT9 : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError → NMT_stage1_owned.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
 | .WrongLength => .WrongLength
 | .WrongMagic => .WrongMagic
 | .WrongVersion => .WrongVersion
 | .WrongTransitionKind => .WrongTransitionKind
 | .WrongDigestEncoding => .WrongDigestEncoding
 | .NonZeroReserved => .NonZeroReserved
 | .ZeroRequiredBinding => .ZeroRequiredBinding
 | .InvalidAnchorSequence => .InvalidAnchorSequence
 | .NonCanonicalDigest => .NonCanonicalDigest
 | .NonCanonicalAssetId => .NonCanonicalAssetId
 | .InvalidWithdrawalAmount => .InvalidWithdrawalAmount
 | .InvalidDestination => .InvalidDestination
 | .InvalidEnvelope => .InvalidEnvelope
 | .EnvelopeMismatch => .EnvelopeMismatch
@[simp] theorem toT9_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : fromT9 (toT9 x) = x := by
 cases x <;> simp [toT9,fromT9]
#print axioms toT9_inverse
@[simp] theorem fromT9_inverse (x : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : toT9 (fromT9 x) = x := by
 cases x <;> simp [fromT9,toT9]
#print axioms fromT9_inverse
end NMT_345Dec
