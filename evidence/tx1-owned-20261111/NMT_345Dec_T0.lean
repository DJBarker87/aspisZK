import NMT_345TransportBase
import NFY_Part058
set_option autoImplicit false
noncomputable section
namespace NMT_345Dec
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT0 : NMT_stage1_owned.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError → AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError
 | .TreeFull => .TreeFull
 | .InsufficientCapacity => .InsufficientCapacity
 | .IndexOutOfRange => .IndexOutOfRange
 | .RootMismatch => .RootMismatch
 | .NonCanonicalFrontier => .NonCanonicalFrontier
 | .WrongLength => .WrongLength
 | .WrongMagic => .WrongMagic
 | .WrongVersion => .WrongVersion
 | .WrongDepth => .WrongDepth
 | .WrongTreeHash => .WrongTreeHash
 | .WrongDigestEncoding => .WrongDigestEncoding
 | .NonCanonicalDigest => .NonCanonicalDigest
 | .NonZeroReserved => .NonZeroReserved
def fromT0 : AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError → NMT_stage1_owned.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError
 | .TreeFull => .TreeFull
 | .InsufficientCapacity => .InsufficientCapacity
 | .IndexOutOfRange => .IndexOutOfRange
 | .RootMismatch => .RootMismatch
 | .NonCanonicalFrontier => .NonCanonicalFrontier
 | .WrongLength => .WrongLength
 | .WrongMagic => .WrongMagic
 | .WrongVersion => .WrongVersion
 | .WrongDepth => .WrongDepth
 | .WrongTreeHash => .WrongTreeHash
 | .WrongDigestEncoding => .WrongDigestEncoding
 | .NonCanonicalDigest => .NonCanonicalDigest
 | .NonZeroReserved => .NonZeroReserved
@[simp] theorem toT0_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError) : fromT0 (toT0 x) = x := by
 cases x <;> simp [toT0,fromT0]
#print axioms toT0_inverse
@[simp] theorem fromT0_inverse (x : AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError) : toT0 (fromT0 x) = x := by
 cases x <;> simp [fromT0,toT0]
#print axioms fromT0_inverse
end NMT_345Dec
