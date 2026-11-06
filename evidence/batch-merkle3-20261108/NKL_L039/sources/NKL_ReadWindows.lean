import NKL_CanonicalWindows
set_option autoImplicit false
noncomputable section
namespace NKL_ReadWindows
open Aeneas Aeneas.Std Result AspisR1
open OraclePortCompactDraft MultiproofConeCanonical NKL_CanonicalWindows

theorem scalar_bytes (q : Slice U8) (s l : Usize) (slot:s.val<4) (lane:l.val<26) :
 bytesOf (NKB_CanonicalScalar.window q s l).val=
 slice (bytesOf q.val) (4*(30*s.val+l.val)) 4 := by
 obtain ⟨a,b⟩:=NKB_CanonicalScalar.address s l slot lane
 simp only [NKB_CanonicalScalar.window,MultiproofConeSlices.bytes_sub]
 rw [a,b]
 congr 1 <;> omega

theorem c1_bytes (q : Slice U8) (s : Usize) (slot:s.val<4) :
 bytesOf (NKB_CanonicalTail.window q s).val=
 slice (bytesOf q.val) (4*(30*s.val+26)) 16 := by
 obtain ⟨a,b⟩:=NKB_CanonicalTail.address s slot
 simp only [NKB_CanonicalTail.window,MultiproofConeSlices.bytes_sub]
 rw [a,b]
 congr 1 <;> omega

theorem c2_bytes (q : Slice U8) (s l : Usize) (slot:s.val<4) (lane:l.val<2) :
 bytesOf (NKB_CanonicalRange.window q s l).val=
 slice (bytesOf q.val) (4*(120+8*s.val+4*l.val)) 16 := by
 obtain ⟨a,b⟩:=NKB_CanonicalRange.address s l slot lane
 simp only [NKB_CanonicalRange.window,MultiproofConeSlices.bytes_sub]
 rw [a,b]
 congr 1 <;> omega

theorem scalar (q : Slice U8) (width:q.val.length=832) (s l : Usize)
 (slot:s.val<4) (lane:l.val<26) :
 NKB_CanonicalScalarLoop.pass NKB_CanonicalScalarBridge.scalar q s l.val=true ↔ W q (30*s.val+l.val) := by
 rw [NKB_CanonicalScalarLoop.actual _ q s l width slot lane,NKB_CanonicalScalarBridge.scalar_tag,NKL_WordCanonical.scalar]
 change canonical (bytesOf (NKB_CanonicalScalar.window q s l).val) ↔ _
 rw [scalar_bytes q s l slot lane]
 have size : (slice (bytesOf q.val) (4*(30*s.val+l.val)) 4).length=4 :=
  NKL_CanonicalWindows.length _ _ _ (by simp only [bytesOf,List.length_map,width];omega)
 rw [NKL_WordCanonical.one _ size]
 rfl

theorem c1 (q : Slice U8) (width:q.val.length=832) (s : Usize) (slot:s.val<4) :
 (NKL_CanonicalKCarrier.selected (NKB_CanonicalTail.window q s)).isSome=true ↔
 ∀ j,j<4→W q (30*s.val+26+j) := by
 rw [NKL_CanonicalWindows.selected _ (NKB_CanonicalDomains.c1 q width s slot),c1_bytes q s slot]
 exact NKL_CanonicalWindows.canonical_window q width (30*s.val+26) 4 (by omega)

theorem c2 (q : Slice U8) (width:q.val.length=832) (s l : Usize) (slot:s.val<4) (lane:l.val<2) :
 (NKL_CanonicalKCarrier.selected (NKB_CanonicalRange.window q s l)).isSome=true ↔
 ∀ j,j<4→W q (120+8*s.val+4*l.val+j) := by
 rw [NKL_CanonicalWindows.selected _ (NKB_CanonicalDomains.c2 q width s l slot lane),c2_bytes q s l slot lane]
 exact NKL_CanonicalWindows.canonical_window q width (120+8*s.val+4*l.val) 4 (by omega)

#print axioms scalar_bytes
#print axioms c1_bytes
#print axioms c2_bytes
#print axioms scalar
#print axioms c1
#print axioms c2
end NKL_ReadWindows
end
