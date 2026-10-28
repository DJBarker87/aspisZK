import NBY_RowCopy

set_option autoImplicit false
namespace AspisR1.NBY_RowCarrier
open Aeneas Aeneas.Std Result MultiproofConeRef

def memory (s : reference.Scratch) (k : Nat) : U8 :=
  s.val.val[k/32]!.val[k%32]!

/-- The SAME flat-memory byte windows produce the actual cohort Array.set
coordinates. No independently selected poststate or assumed final-array
identity occurs. This is a value-carrier theorem; the native call association
and oracle-history association remain separate obligations. -/
theorem installed_bytes (s : reference.Scratch) (w : Usize)
    (digest : MultiproofConePhysicalLive.Digest) (j c : Nat)
    (wb : w.val < 16) (jb : j < 16) (cb : c < 32) :
    NBY_RowCopy.byteWindows (fun k => digest.val[k-32*w.val]!)
      (memory s) (32*w.val) 32 (32*j+c) =
      (s.val.set w digest).val[j]!.val[c]! := by
  rw [NBY_RowCopy.row_cells (memory s) (fun k => digest.val[k]!) w.val j c cb]
  rw [MultiproofConePhysicalDigest.set_digest s w digest wb j jb]
  by_cases same : j = w.val
  · simp only [if_pos same]
  · simp only [if_neg same,memory]
    have quotient : (32*j+c)/32 = j := by omega
    have remainder : (32*j+c)%32 = c := by omega
    rw [quotient,remainder]

#print axioms installed_bytes
end AspisR1.NBY_RowCarrier
