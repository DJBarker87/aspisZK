import R1CanonicalLogInputs
import R1CanonicalReadCollision

/-! Hash separation of the canonical records is derived from the existing
full-trace collision exclusion, not assumed as a new cryptographic premise. -/
set_option autoImplicit false
namespace AspisR1.CanonicalLogSeparation

open FS FS2.Duplex
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
open AspisV8R19.MemoizedProgramLaw
open CanonicalByteHash

variable {M Cv : Type} {L : Nat}

theorem separated (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre tr : List (Addr L × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hread : ∀ a, Read pre a → Read tr a)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hno : ¬ hitsBad (badColl p Qtot) emptyTable tr) :
    ∀ a b da db,
      (a, da) ∈ CanonicalOracleLog.byteLog pre →
      (b, db) ∈ CanonicalOracleLog.byteLog pre →
      hashBytes H a = hashBytes H b → a = b := by
  intro a b da db ha hb heq
  have hain : a ∈ (CanonicalOracleLog.byteLog pre).map Prod.fst :=
    List.mem_map.mpr ⟨(a, da), ha, rfl⟩
  have hbin : b ∈ (CanonicalOracleLog.byteLog pre).map Prod.fst :=
    List.mem_map.mpr ⟨(b, db), hb, rfl⟩
  by_contra hne
  exact noColl_injective p Qtot H tr hcons hQ hno (encode a) (encode b)
    (hread _ (CanonicalLogInputs.input_read hain))
    (hread _ (CanonicalLogInputs.input_read hbin))
    (CanonicalLogInputs.encode_ne (CanonicalLogInputs.input_length_le hain)
      (CanonicalLogInputs.input_length_le hbin) hne) heq

theorem self_separated (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (tr : List (Addr L × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hno : ¬ hitsBad (badColl p Qtot) emptyTable tr) :
    ∀ a b da db,
      (a, da) ∈ CanonicalOracleLog.byteLog tr →
      (b, db) ∈ CanonicalOracleLog.byteLog tr →
      hashBytes H a = hashBytes H b → a = b := by
  exact separated p Qtot H tr tr hcons (fun _ h => h) hQ hno

#print axioms separated
#print axioms self_separated

end AspisR1.CanonicalLogSeparation
