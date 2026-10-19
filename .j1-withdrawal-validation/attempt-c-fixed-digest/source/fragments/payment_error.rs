#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PaymentStatementFormatError {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongTransitionKind,
    WrongDigestEncoding,
    NonZeroReserved,
    ZeroRequiredBinding,
    InvalidAnchorSequence,
    NonCanonicalDigest,
    NonCanonicalAssetId,
    InvalidWithdrawalAmount,
    InvalidDestination,
    InvalidEnvelope,
    EnvelopeMismatch,
}