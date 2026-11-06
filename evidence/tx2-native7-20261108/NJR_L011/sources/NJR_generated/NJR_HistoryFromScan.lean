import Op4P_Install
import MultiproofConeSliceComposition
import NJR_FinishWindows
set_option autoImplicit false
noncomputable section
namespace NJR_HistoryFromScan
open Aeneas Aeneas.Std AspisR1
open OraclePortCompactDraft MultiproofConeCanonical

theorem little_word (xs : List U8) (size : xs.length=4) :
 little (bytesOf xs)=NIG_FinishInput.word xs 0 := by
 cases xs with
 | nil => simp at size
 | cons a xs => cases xs with
  | nil => simp at size
  | cons b xs => cases xs with
   | nil => simp at size
   | cons c xs => cases xs with
    | nil => simp at size
    | cons d xs => cases xs with
     | nil =>
       simp [little,bytesOf,AspisV8R19.SqueezeOracleBridge.decodeByte,NIG_FinishInput.word]
       omega
     | cons e xs => simp at size

/-- Symbolic transport of an arbitrary aligned word in a scanned region. -/
theorem region (proof : Slice U8) (lo count : Nat)
 (bound : lo+4*count≤proof.val.length)
 (checked : canonical (slice (bytesOf proof.val) lo (4*count)))
 (t : Nat) (inside : t<count) :
 NIG_FinishInput.word proof.val (lo+4*t)<2147483647 := by
 have len : (slice (bytesOf proof.val) lo (4*count)).length=4*count := by
  simp only [slice,bytesOf,List.length_take,List.length_drop,List.length_map]
  omega
 have h:=checked.2 t (by simp only [List.mem_range,len];omega)
 rw [MultiproofConeSliceComposition.slice_slice _ lo (4*count) (4*t) 4 (by omega)] at h
 have rawLen : ((proof.val.drop (lo+4*t)).take 4).length=4 := by
  simp only [List.length_take,List.length_drop];omega
 have same : slice (bytesOf proof.val) (lo+4*t) 4=
  bytesOf ((proof.val.drop (lo+4*t)).take 4) := by
  simp only [slice,bytesOf,List.map_take,List.map_drop]
 rw [same,little_word _ rawLen,NJR_FinishWindows.word_window _ (lo+4*t) 4 0 (by omega)] at h
 simpa only [Nat.add_zero] using h

/-- The existing strict scanner's SAME returned success gives every raw word
required by finish. This discharges the mathematical history implication,
while binding that TX1 scan to TX2's actual proof remains a physical caller
obligation. No successful history is added as a positive-root premise. -/
theorem source (proof : Slice U8) (length : proof.val.length=57607)
 (success : Op4P_Install.sourceBody proof = .ok (.Ok ())) :
 NJR_FinishWindows.History proof := by
 have scan:=Op4P_Install.scan_of_success proof length success
 refine ⟨?_,?_,?_⟩
 · intro i hi j hj
   have h:=region proof 7495 64 (by omega) scan.2.1 (8+8*i+j) (by omega)
   convert h using 1 <;> congr 1 <;> omega
 · intro i hi j hj
   have h:=region proof 7783 568 (by omega) scan.2.2.1 (8*i+j) (by omega)
   convert h using 1 <;> congr 1 <;> omega
 · intro i hi j hj
   have h:=region proof 7783 568 (by omega) scan.2.2.1 (56+8*i+j) (by omega)
   convert h using 1 <;> congr 1 <;> omega

#print axioms little_word
#print axioms region
#print axioms source
end NJR_HistoryFromScan
