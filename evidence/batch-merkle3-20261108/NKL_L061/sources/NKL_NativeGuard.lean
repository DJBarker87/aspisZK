import NKL_ScanAtoms
import NKL_CanonicalK
set_option autoImplicit false
noncomputable section
namespace NKL_NativeGuard
open Aeneas Aeneas.Std Result AspisR1 NKL_Checks

def kGuard (bytes:Slice U8) : Bool :=
 if h:bytes.val.length=16 then NKL_CanonicalK.guard ⟨bytes.val,h⟩ else false

/-- The concrete native postcondition: scalar/four-word byte guards; for
logged EC/CV replies the complete CLOSED child, never a free outcome. -/
def nativeGuard : Check→Bool
 | .cv proof=>NKL_ScanAtoms.accepted (.cv proof)
 | .ec site=>NKL_ScanAtoms.accepted (.ec site)
 | .view _ _=>true
 | .scalar q s l=>match NKB_CanonicalScalarLoop.read q s l with
   | none=>false | some b=>NKB_CanonicalScalarBridge.good b
 | .c1 q s=>kGuard (NKB_CanonicalTail.window q s)
 | .c2 q s l=>kGuard (NKB_CanonicalRange.window q s l)
 | .invalid=>false

theorem k (bytes:Slice U8) (width:bytes.val.length=16) :
 kGuard bytes=(NKL_CanonicalKCarrier.selected bytes).isSome := by
 let b:Array U8 16#usize:=⟨bytes.val,width⟩
 have same:b.to_slice=bytes := by apply Subtype.ext;rfl
 have h:=NKL_CanonicalKCarrier.selected_tag b
 rw [same,NKL_CanonicalK.good_eq_guard] at h
 exact (by simpa only [kGuard,dif_pos width] using h.symm)

theorem source (c:Check) (domain:NKL_ScanDomains.Domain c) : nativeGuard c=test c := by
 cases c with
 | cv proof=>exact NKL_ScanAtoms.accepted_test _ domain
 | ec site=>exact NKL_ScanAtoms.accepted_test _ domain
 | view proof i=>
   obtain ⟨q,read,_,_⟩:=NKL_ClosedChildren.opening proof domain.1 i domain.2
   simp only [nativeGuard,test,read]
 | scalar q s l=>
   cases read:NKB_CanonicalScalarLoop.read q s l with
   | none=>simp only [nativeGuard,test,read,Option.bind_none,Option.isSome_none]
   | some b=>simp only [nativeGuard,test,read,Option.bind_some,NKB_CanonicalScalarBridge.scalar_tag]
 | c1 q s=>exact k _ (NKB_CanonicalDomains.c1 q domain.1 s domain.2)
 | c2 q s l=>exact k _ (NKB_CanonicalDomains.c2 q domain.1 s l domain.2.1 domain.2.2)
 | invalid=>exact False.elim domain

#print axioms k
#print axioms source
end NKL_NativeGuard
end
