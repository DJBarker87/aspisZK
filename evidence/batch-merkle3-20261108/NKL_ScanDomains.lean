import NKL_Checks
import NKL_ClosedChildren
set_option autoImplicit false
noncomputable section
namespace NKL_ScanDomains
open Aeneas Aeneas.Std Result AspisR1 NKL_Checks

def Domain : Check→Prop
 | .cv proof => proof.val.length=57607
 | .ec (.inactive proof) => proof.val.length=57607
 | .ec (.round0 proof) => proof.val.length=57607
 | .ec (.round1 proof) => proof.val.length=57607
 | .ec (.tail q) => q.val.length=832
 | .view proof i => proof.val.length=57607 ∧ i.val<22
 | .scalar q s l => q.val.length=832 ∧ s.val<4 ∧ l.val<26
 | .c1 q s => q.val.length=832 ∧ s.val<4
 | .c2 q s l => q.val.length=832 ∧ s.val<4 ∧ l.val<2
 | .invalid => False

theorem slot (q : Slice U8) (width:q.val.length=832) (s : Nat) (bound:s<4) :
 ∀ c∈NKL_Checks.slot q s,Domain c := by
 have sv:(NKB_CanonicalScalarLoop.index s).val=s := NKL_CanonicalWindows.index s (by omega)
 intro c member
 simp only [NKL_Checks.slot,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with scalar | same | same | same
 · obtain ⟨l,lane,rfl⟩:=scalar
   have lv:(NKB_CanonicalScalarLoop.index l).val=l := NKL_CanonicalWindows.index l (by have h:=List.mem_range.mp lane;omega)
   exact ⟨width,by rw [sv];exact bound,by rw [lv];exact List.mem_range.mp lane⟩
 · subst c;exact ⟨width,by rw [sv];exact bound⟩
 · subst c;exact ⟨width,by rw [sv];exact bound,by decide⟩
 · subst c;exact ⟨width,by rw [sv];exact bound,by decide⟩

theorem opening (q : Slice U8) (width:q.val.length=832) :
 ∀ c∈NKL_Checks.opening q,Domain c := by
 intro c member
 simp only [NKL_Checks.opening,List.mem_append,List.mem_flatMap,List.mem_singleton] at member
 rcases member with ⟨s,range,member⟩ | rfl
 · exact slot q width s (List.mem_range.mp range) c member
 · exact width

theorem row (proof : Slice U8) (width:proof.val.length=57607) (i : Nat) (bound:i<22) :
 ∀ c∈NKL_Checks.row proof i,Domain c := by
 have iv:(NKB_CanonicalScalarLoop.index i).val=i := NKL_CanonicalWindows.index i (by omega)
 obtain ⟨q,read,len,_⟩:=NKL_ClosedChildren.opening proof width (NKB_CanonicalScalarLoop.index i) (by rw [iv];exact bound)
 unfold NKL_Checks.row
 rw [read]
 intro c member
 simp only [List.mem_cons] at member
 rcases member with rfl|tail
 · exact ⟨width,by rw [iv];exact bound⟩
 · exact opening q len c tail

theorem header (proof : Slice U8) (width:proof.val.length=57607) :
 ∀ c∈NKL_Checks.header proof,Domain c := by
 obtain ⟨y,a,b,d⟩:=NKB_CanonicalDomains.prefix_windows proof width
 intro c member
 simp only [NKL_Checks.header,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl <;> exact width

/-- Every native and CLOSED child domain is discharged at the SAME original
proof. No canonicality, child success, independent opening, or callback law. -/
theorem source (proof : Slice U8) (width:proof.val.length=57607) :
 ∀ c∈NKL_Checks.checks proof,Domain c := by
 intro c member
 simp only [NKL_Checks.checks,List.mem_append,List.mem_flatMap] at member
 rcases member with head|⟨i,range,member⟩
 · exact header proof width c head
 · exact row proof width i (List.mem_range.mp range) c member

set_option pp.proofs false
#print source
#print axioms slot
#print axioms opening
#print axioms row
#print axioms header
#print axioms source
end NKL_ScanDomains
end
