import NKL_CanonicalInstallation
import NKL_ChildCanonical
import NKL_CanonicalConcat
set_option autoImplicit false
noncomputable section
namespace NKL_PrefixCanonical
open Aeneas Aeneas.Std Result AspisR1
open OraclePortCompactDraft MultiproofConeCanonical
open NKB_CanonicalPrefix

def model (proof : Slice U8) : Prop :=
 canonical (slice (bytesOf proof.val) 7031 464) ∧
 canonical (slice (bytesOf proof.val) 7495 256) ∧
 canonical (slice (bytesOf proof.val) 7783 2272)

theorem slice_join (bs : AspisV8R19.DuplexFrames.Bytes) (offset left right : Nat) :
 slice bs offset (left+right)=slice bs offset left++slice bs (offset+left) right := by
 simp only [slice,List.take_add,List.drop_drop,Nat.add_comm]

theorem source (proof : Slice U8) (width:proof.val.length=57607) :
 guard NKL_CanonicalChildren.compactGood NKL_CanonicalChildren.echeckGood proof=true ↔ model proof := by
 obtain ⟨y,a,b,c⟩:=NKB_CanonicalDomains.prefix_windows proof width
 have cv:=NKL_ChildCanonical.compact (values proof) (by omega)
 have ea:=NKL_ChildCanonical.echeck (inactive proof) (by omega)
 have eb:=NKL_ChildCanonical.echeck (round0 proof) (by omega)
 have ec:=NKL_ChildCanonical.echeck (round1 proof) (by omega)
 have expanded : guard NKL_CanonicalChildren.compactGood NKL_CanonicalChildren.echeckGood proof=true ↔
  canonical (bytesOf (values proof).val) ∧ canonical (bytesOf (inactive proof).val) ∧
  canonical (bytesOf (round0 proof).val) ∧ canonical (bytesOf (round1 proof).val) := by
  unfold NKB_CanonicalPrefix.guard
  simp only [Bool.and_eq_true]
  rw [cv,ea,eb,ec]
  exact and_assoc.trans (and_congr Iff.rfl and_assoc)
 have merge:=NKL_CanonicalConcat.append (bytesOf (inactive proof).val) (bytesOf (round0 proof).val)
   (by simp only [bytesOf,List.length_map,a])
 have joined : bytesOf (inactive proof).val++bytesOf (round0 proof).val=
   slice (bytesOf proof.val) 7495 256 := by
  simp only [inactive,round0,MultiproofConeSlices.bytes_sub]
  exact (slice_join (bytesOf proof.val) 7495 32 224).symm
 have vy : bytesOf (values proof).val=slice (bytesOf proof.val) 7031 464 := by
  simp only [values,MultiproofConeSlices.bytes_sub];rfl
 have vc : bytesOf (round1 proof).val=slice (bytesOf proof.val) 7783 2272 := by
  simp only [round1,MultiproofConeSlices.bytes_sub];rfl
 rw [joined] at merge
 rw [expanded]
 unfold model
 constructor
 · rintro ⟨hy,ha,hb,hc⟩
   exact ⟨by simpa only [vy] using hy,merge.mpr ⟨ha,hb⟩,by simpa only [vc] using hc⟩
 · rintro ⟨hy,hab,hc⟩
   obtain ⟨ha,hb⟩:=merge.mp hab
   exact ⟨by simpa only [vy] using hy,ha,hb,by simpa only [vc] using hc⟩

#print axioms slice_join
#print axioms source
end NKL_PrefixCanonical
end
