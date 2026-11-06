import NKK_EmbedRaw
import NKK_RawAssociation
import NKK_RawSynchrony
set_option autoImplicit false
noncomputable section
namespace NKK_RawPrefix
open Aeneas Aeneas.Std Result NKK_NativeRaw

def run (n : Usize) (count : Nat) (r : Reader) :=
 NKK_EmbedRaw.run NKK_EmbedRaw.event (NKK_RawFold.observed n count r)

/-- A literal raw stage assembled from native one-event windows. -/
def literal (n : Usize) : Nat → Reader →
 NJU_Log.Run NJU_ResumeObserved.Event (List (Array U8 n) × Reader)
 | 0,r => pure ([],r)
 | count+1,r => do
   let (b,next) ← NJU_ResumeObserved.recordRaw n r
   let (bs,last) ← literal n count next
   pure (b::bs,last)

theorem source (n : Usize) (count : Nat) (r : Reader) : run n count r=literal n count r := by
 induction count generalizing r with
 | zero => rfl
 | succ count ih =>
  unfold run NKK_RawFold.observed
  rw [NKK_EmbedRaw.bind,NKK_EmbedRaw.raw]
  congr 1
  funext pair
  rcases pair with ⟨b,next⟩
  rw [NKK_EmbedRaw.bind]
  change ((run n count next) >>= fun pair=>pure (b::pair.1,pair.2))=_
  rw [ih]
  rfl

/-- Native fold induction and the literal source use this one computed log. -/
theorem associated (n : Usize) (count : Nat) (r : Reader)
 (before : List (Array U8 n)) :
 NKK_RawFold.Matches before
 (NKK_RawFold.fold (NKK_RawFold.observed n count r).events ⟨before,r,.ok ()⟩)
 (literal n count r).result := by
 rw [←source]
 exact NKK_RawFold.association n count r before

#print axioms source
#print axioms associated
end NKK_RawPrefix
