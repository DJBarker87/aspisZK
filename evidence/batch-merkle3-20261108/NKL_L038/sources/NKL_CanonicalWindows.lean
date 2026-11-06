import NKL_WordCanonical
import NKL_CanonicalInstallation
set_option autoImplicit false
noncomputable section
namespace NKL_CanonicalWindows
open Aeneas Aeneas.Std Result AspisR1
open OraclePortCompactDraft MultiproofConeCanonical
open NKB_CanonicalRange
attribute [local instance] Classical.propDecidable

def W (q : Slice U8) (j : Nat) : Prop :=
 little (slice (bytesOf q.val) (4*j) 4)<2147483647

theorem nested (bs : AspisV8R19.DuplexFrames.Bytes) (offset size start count : Nat)
 (inside:start+count≤size) :
 slice (slice bs offset size) start count=slice bs (offset+start) count := by
 simp only [slice]
 rw [List.drop_take,List.take_take]
 have min : min count (size-start)=count := by omega
 rw [min,List.drop_drop]

theorem length (bs : AspisV8R19.DuplexFrames.Bytes) (offset size : Nat)
 (inside:offset+size≤bs.length) : (slice bs offset size).length=size := by
 simp only [slice,List.length_take,List.length_drop]
 omega

theorem canonical_window (q : Slice U8) (width:q.val.length=832) (start count : Nat)
 (inside:4*start+4*count≤832) :
 canonical (slice (bytesOf q.val) (4*start) (4*count)) ↔ ∀ j,j<count→W q (start+j) := by
 have size : (slice (bytesOf q.val) (4*start) (4*count)).length=4*count :=
  length _ _ _ (by simp only [bytesOf,List.length_map,width];exact inside)
 unfold canonical
 rw [size]
 simp only [Nat.mul_mod_right,Nat.mul_div_right,true_and,List.mem_range]
 apply forall_congr'
 intro j
 apply imp_congr_right
 intro bound
 rw [nested _ (4*start) (4*count) (4*j) 4 (by omega)]
 unfold W
 have addr : 4*start+4*j=4*(start+j) := by omega
 rw [addr]

theorem index (n : Nat) (bound:n<32) : (NKB_CanonicalScalarLoop.index n).val=n := by
 change n%32=n
 exact Nat.mod_eq_of_lt bound

theorem allFrom (pass : Nat→Bool) (start fuel : Nat) :
 NKB_CanonicalPair.allFrom pass start fuel=true ↔ ∀ j,start≤j→j<start+fuel→pass j=true := by
 induction fuel generalizing start with
 | zero => simp [NKB_CanonicalPair.allFrom]
 | succ fuel ih =>
   rw [NKB_CanonicalPair.allFrom,Bool.and_eq_true,ih]
   constructor
   · rintro ⟨head,tail⟩ j lo hi
     by_cases same:j=start
     · simpa only [same] using head
     · exact tail j (by omega) (by omega)
   · intro all
     exact ⟨all start (by omega) (by omega),fun j lo hi=>all j (by omega) (by omega)⟩

theorem selected (bytes : Slice U8) (width:bytes.val.length=16) :
 (NKL_CanonicalKCarrier.selected bytes).isSome=true ↔ canonical (bytesOf bytes.val) := by
 let b : Array U8 16#usize:=⟨bytes.val,width⟩
 have same : b.to_slice=bytes := by apply Subtype.ext;rfl
 rw [←same,NKL_CanonicalKCarrier.selected_tag]
 exact NKL_WordCanonical.k b

#print axioms nested
#print axioms length
#print axioms canonical_window
#print axioms index
#print axioms allFrom
#print axioms selected
end NKL_CanonicalWindows
end
