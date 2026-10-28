import R1Z.PDict_Publication
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ErrorKind
open Aeneas Aeneas.Std Result ProverRwFull
deriving instance DecidableEq for ProverRwFull.core.io.error.ErrorKind
def eq
  (self : ProverRwFull.core.io.error.ErrorKind) (other : ProverRwFull.core.io.error.ErrorKind) :
  Result Bool
  := do
  let self1 := read_discriminant self
  let other1 := read_discriminant other
  ok (self1 = other1)

def decode (code : Isize) : Option ProverRwFull.core.io.error.ErrorKind :=
  match code.val with
  | 0 => some .NotFound
  | 1 => some .PermissionDenied
  | 2 => some .ConnectionRefused
  | 3 => some .ConnectionReset
  | 4 => some .HostUnreachable
  | 5 => some .NetworkUnreachable
  | 6 => some .ConnectionAborted
  | 7 => some .NotConnected
  | 8 => some .AddrInUse
  | 9 => some .AddrNotAvailable
  | 10 => some .NetworkDown
  | 11 => some .BrokenPipe
  | 12 => some .AlreadyExists
  | 13 => some .WouldBlock
  | 14 => some .NotADirectory
  | 15 => some .IsADirectory
  | 16 => some .DirectoryNotEmpty
  | 17 => some .ReadOnlyFilesystem
  | 18 => some .FilesystemLoop
  | 19 => some .StaleNetworkFileHandle
  | 20 => some .InvalidInput
  | 21 => some .InvalidData
  | 22 => some .TimedOut
  | 23 => some .WriteZero
  | 24 => some .StorageFull
  | 25 => some .NotSeekable
  | 26 => some .QuotaExceeded
  | 27 => some .FileTooLarge
  | 28 => some .ResourceBusy
  | 29 => some .ExecutableFileBusy
  | 30 => some .Deadlock
  | 31 => some .CrossesDevices
  | 32 => some .TooManyLinks
  | 33 => some .InvalidFilename
  | 34 => some .ArgumentListTooLong
  | 35 => some .Interrupted
  | 36 => some .Unsupported
  | 37 => some .UnexpectedEof
  | 38 => some .OutOfMemory
  | 39 => some .InProgress
  | 40 => some .Other
  | 41 => some .Uncategorized
  | _ => none

theorem decode_encode (x : ProverRwFull.core.io.error.ErrorKind) :
    decode (read_discriminant x) = some x := by
  cases x <;> simp [decode, read_discriminant, ProverRwFull.core.io.error.ErrorKind.read_discriminant]

theorem discriminant_injective : Function.Injective
    (fun x : ProverRwFull.core.io.error.ErrorKind => (read_discriminant x : Isize)) := by
  intro a b h
  have h' := congrArg decode h
  rw [decode_encode, decode_encode] at h'
  exact Option.some.inj h'

theorem eq_exact (a b : ProverRwFull.core.io.error.ErrorKind) :
    eq a b = .ok (decide (a = b)) := by
  simp only [eq, discriminant_injective.eq_iff]

#print axioms decode_encode
#print axioms discriminant_injective
#print axioms eq_exact
end R1Z.PDict_ErrorKind
