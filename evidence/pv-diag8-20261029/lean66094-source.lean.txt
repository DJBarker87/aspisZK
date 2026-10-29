import PV_DIAG8_Frames
set_option autoImplicit false
namespace PV_DIAG8
/-! The six fields printed as plan::prove's mask_audit are fixed by the
successful return guards, even though their computations read mask data. -/
structure MaskAudit where
 c1 : Nat
 maskOnly : Nat
 d : Bool
 g : Bool
 padding : Bool
 total : Bool
 deriving DecidableEq

def auditLiteral : MaskAudit := ⟨16,10,true,true,true,true⟩
def auditGate (a : MaskAudit) : Option MaskAudit :=
 if a.c1=16 ∧ a.maskOnly=10 ∧ a.d=true ∧ a.g=true ∧ a.padding=true then
   some {a with total := true}
 else none

theorem audit_success_literal (a returned : MaskAudit)
    (h : auditGate a = some returned) : returned = auditLiteral := by
  unfold auditGate at h
  split at h
  next hg =>
    cases h
    cases a
    simp_all [auditLiteral]
  next hg => cases h
#print axioms audit_success_literal

theorem audit_formatter_public {O : Type} (format : MaskAudit → O)
    (a b x y : MaskAudit) (hx : auditGate a=some x) (hy : auditGate b=some y) :
    format x = format y := by
  rw [audit_success_literal a x hx,audit_success_literal b y hy]
#print axioms audit_formatter_public

theorem native_folded_slice_guard (u : Nat) (h : u < 262144) :
    4*(u/4)+4 ≤ 262144 ∧ u/4 < 262144 := by omega
#print axioms native_folded_slice_guard

theorem compact_layout_guard :
    16+7015+464+32+224+32+224+2048=10055 ∧
    10055+22*832=28359 ∧
    28359+32*(146+146+128+172+172+150)=57607 := by decide
#print axioms compact_layout_guard
end PV_DIAG8
