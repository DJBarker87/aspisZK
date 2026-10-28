import R1Z.PV_RDEA_ReservationName
import R1Z.PV_RDEA_JoinRequests
namespace R1Z.PV_RDEA_ProtocolSites
open PV_RDEA_PathSchedule PV_RDEA_PathBranches

inductive Site where
  | noteRecovery
  | maskNonceLedger
  | proof
  | statement
  | reservation
  deriving DecidableEq

/-- Exact byte counts of the five literal/hex-encoded application arguments.
Their source spellings are checked by the call-site binding script. -/
def argumentLength : Site → Nat
  | .noteRecovery => 18
  | .maskNonceLedger => 17
  | .proof => 9
  | .statement => 13
  | .reservation => 69

def requestWord (site : Site) (baseLen : Nat) (needSep : Bool) :=
  joinWord baseLen (argumentLength site) false needSep

/-- Path-data classification is explicit: only the public base length and
trailing-separator predicate enter; no witness or basename contents occur. -/
def requestsFor {W : Type} (site : Site) (baseLen : Nat) (needSep : Bool) (_witness : W) :=
  requestWord site baseLen needSep

theorem witness_independent {W : Type} (site : Site) (baseLen : Nat) (needSep : Bool)
    (w1 w2 : W) : requestsFor site baseLen needSep w1=requestsFor site baseLen needSep w2 := rfl

/-- Stronger than public-nonce provenance: even a secret digest cannot change
reservation basename length or the relative-path allocation word. -/
theorem reservation_word (digest : List (Fin 256)) (size : digest.length=32)
    (baseLen : Nat) (needSep : Bool) :
    joinWord baseLen (PV_RDEA_ReservationName.basename digest).length false needSep =
      requestWord .reservation baseLen needSep := by
  rw [PV_RDEA_ReservationName.fixed_name_length digest size]
  rfl

theorem request_word_public (site : Site) (baseLen baseLen' : Nat) (needSep needSep' : Bool)
    (sameLength : baseLen=baseLen') (sameSeparator : needSep=needSep') :
    requestWord site baseLen needSep=requestWord site baseLen' needSep' := by
  rw [sameLength,sameSeparator]

#print axioms witness_independent
#print axioms reservation_word
#print axioms request_word_public
end R1Z.PV_RDEA_ProtocolSites
