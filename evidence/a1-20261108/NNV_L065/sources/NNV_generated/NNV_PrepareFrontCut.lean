import NNH_Libraries
import NNH_PrepareReturns
import NNH_ExceptOk
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_PrepareFrontCut
open RSL NNH_Libraries NNH_ReturnedRE
abbrev V := NNH_PrepareReturns.V
/-- Unmapping retains precisely the successful value; no liveness assumption. -/
theorem unmap {E F A : Type} (f : E → F) (r : Except E A) (a : A)
 (h : RE.mapE f r = .ok a) : r = .ok a := by
 cases r with
 | error e => cases h
 | ok b => exact congrArg Except.ok (Except.ok.inj h)
structure Packet (a : TX1_087.Args V) (env : Env) (sem : Verified V) (v : V.View) where
 logical : Bytes
 semantic : Bytes
 y1 : Bytes
 filled : LIB_VLib.filledValue (LOGICAL_SEMANTIC+LOGICAL_Y1) env = .ok logical
 expandedSemantic : LIB_VLib.expandSemanticValue
  (slice a.proof OFF_SEMANTIC OFF_Y1,logical.take LOGICAL_SEMANTIC) env = .ok semantic
 expandedValues : LIB_VLib.expandValuesValue
  (slice a.proof OFF_Y1 OFF_INACTIVE,logical.drop LOGICAL_SEMANTIC) env = .ok y1
 viewed : LIB_VLib.wideViewValue (a.proof,semantic,y1) env = .ok v
 observed : NNH_ObservedReturns.value ⟨a.public_,V.viewSemantic v⟩ env = .ok sem

theorem returned (a : TX1_087.Args V) (env : Env) (sem : Verified V) (v : V.View)
 (called : NNH_PrepareReturns.frontValue a env = .ok (sem,v)) :
 Nonempty (Packet a env sem v) := by
 unfold NNH_PrepareReturns.frontValue at called
 obtain ⟨logical,hl,called⟩ := NNH_ExceptOk.bind _ _ (sem,v) called
 obtain ⟨semantic,hs,called⟩ := NNH_ExceptOk.bind _ _ (sem,v) called
 obtain ⟨y1,hy,called⟩ := NNH_ExceptOk.bind _ _ (sem,v) called
 obtain ⟨view,hv,called⟩ := NNH_ExceptOk.bind _ _ (sem,v) called
 obtain ⟨s,ho,same⟩ := NNH_ExceptOk.bind _ _ (sem,v) called
 have image : (s,view)=(sem,v) := Except.ok.inj same
 cases image
 exact ⟨⟨logical,semantic,y1,unmap _ _ _ hl,unmap _ _ _ hs,unmap _ _ _ hy,hv,unmap _ _ _ ho⟩⟩
#print axioms unmap
#print axioms returned
end AspisR1.NNV_PrepareFrontCut
end
