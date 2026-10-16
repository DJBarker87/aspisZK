import AspisR1TerminalDecoder.Types

-- The identical file is checked with original and naming-adapted Types.
open Aeneas Aeneas.Std
namespace AspisR1TerminalDecoder.PaymentDiscriminantAudit
open pool_v1.payment_relation

def codes : List Isize :=
  [read_discriminant (PoolV1PaymentStatementFormatError.WrongLength),
   read_discriminant (PoolV1PaymentStatementFormatError.WrongMagic),
   read_discriminant (PoolV1PaymentStatementFormatError.WrongVersion),
   read_discriminant (PoolV1PaymentStatementFormatError.WrongTransitionKind),
   read_discriminant (PoolV1PaymentStatementFormatError.WrongDigestEncoding),
   read_discriminant (PoolV1PaymentStatementFormatError.NonZeroReserved),
   read_discriminant (PoolV1PaymentStatementFormatError.ZeroRequiredBinding),
   read_discriminant (PoolV1PaymentStatementFormatError.InvalidAnchorSequence),
   read_discriminant (PoolV1PaymentStatementFormatError.NonCanonicalDigest),
   read_discriminant (PoolV1PaymentStatementFormatError.NonCanonicalAssetId),
   read_discriminant (PoolV1PaymentStatementFormatError.InvalidWithdrawalAmount),
   read_discriminant (PoolV1PaymentStatementFormatError.InvalidDestination),
   read_discriminant (PoolV1PaymentStatementFormatError.InvalidEnvelope),
   read_discriminant (PoolV1PaymentStatementFormatError.EnvelopeMismatch)]

theorem codes_eq : codes =
    [0#isize, 1#isize, 2#isize, 3#isize, 4#isize, 5#isize, 6#isize, 7#isize, 8#isize, 9#isize, 10#isize, 11#isize, 12#isize, 13#isize] := rfl

#print axioms codes_eq
end AspisR1TerminalDecoder.PaymentDiscriminantAudit
