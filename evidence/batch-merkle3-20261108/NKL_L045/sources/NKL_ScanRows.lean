import NKL_OpeningCanonical
import Port4B_Opening
set_option autoImplicit false
noncomputable section
namespace NKL_ScanRows
open Aeneas Aeneas.Std Result AspisR1
open OraclePortCompactDraft MultiproofConeCanonical

theorem one (proof : Slice U8) (width:proof.val.length=57607) (i : Usize) (bound:i.val<22) :
 NKB_CanonicalRows.pass NKB_CanonicalScalarBridge.scalar NKL_CanonicalKCarrier.selected
  NKL_CanonicalChildren.echeckGood proof i.val=true ↔
 openingCanonical (slice (bytesOf proof.val) (10055+i.val*832) 832) := by
 obtain ⟨q,read,len,bytes⟩:=Port4B_Opening.opening_exact proof width i bound
 rw [←NKB_CanonicalRows.opening] at read
 rw [NKB_CanonicalRows.actual _ _ _ proof i bound]
 unfold NKB_CanonicalRows.accepted
 rw [read]
 change NKL_OpeningCanonical.native q=true ↔ _
 rw [NKL_OpeningCanonical.source q len,bytes]

theorem source (proof : Slice U8) (width:proof.val.length=57607) :
 NKB_CanonicalPair.allFrom
  (NKB_CanonicalRows.pass NKB_CanonicalScalarBridge.scalar NKL_CanonicalKCarrier.selected
   NKL_CanonicalChildren.echeckGood proof) 0 22=true ↔
 ∀ j∈List.range 22,openingCanonical (slice (bytesOf proof.val) (10055+j*832) 832) := by
 rw [NKL_CanonicalWindows.allFrom]
 simp only [Nat.zero_add,Nat.zero_le,true_implies,List.mem_range]
 apply forall_congr'
 intro i
 apply imp_congr_right
 intro bound
 have iv:(NKB_CanonicalScalarLoop.index i).val=i := NKL_CanonicalWindows.index i (by omega)
 have h:=one proof width (NKB_CanonicalScalarLoop.index i) (by rw [iv];exact bound)
 simpa only [iv] using h

#print axioms one
#print axioms source
end NKL_ScanRows
end
