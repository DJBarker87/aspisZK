import NFC_DotDomain
import NFA_FourCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFC_FourDomain
open Aeneas Aeneas.Std Result NEV_DotCarrier
/-- Four ordered child domains and output coordinates on the SAME converted
source prefix. Incoming coefficient canonicality is still a caller obligation. -/
theorem accepted (q : Slice U8) (g : NEV_DotInputs.Coefficients)
    (canonical : NEV_DotInputs.Canonical g) (out : Array NE 4#usize)
    (run : FIp_NativeDots.fast_dots.four_dots q g=ok out) :
    (∀ value∈out.val,canonE value) ∧
    ∃ fixed a b c d,
      FIp_NativeDots.fast_dots.four_dots_one fixed g 0#usize=ok a ∧
      FIp_NativeDots.fast_dots.four_dots_one fixed g 1#usize=ok b ∧
      FIp_NativeDots.fast_dots.four_dots_one fixed g 2#usize=ok c ∧
      FIp_NativeDots.fast_dots.four_dots_one fixed g 3#usize=ok d ∧
      canonE a ∧ canonE b ∧ canonE c ∧ canonE d ∧ out=Array.make 4#usize [a,b,c,d] := by
  obtain ⟨window,converted,fixed,a,b,c,d,_,_,_,ca,cb,cc,cd,shape⟩:=NFA_FourCuts.actual q g out run
  have ha:=(NFC_DotDomain.accepted fixed g 0#usize a canonical ca).1
  have hb:=(NFC_DotDomain.accepted fixed g 1#usize b canonical cb).1
  have hc:=(NFC_DotDomain.accepted fixed g 2#usize c canonical cc).1
  have hd:=(NFC_DotDomain.accepted fixed g 3#usize d canonical cd).1
  refine ⟨?_,fixed,a,b,c,d,ca,cb,cc,cd,ha,hb,hc,hd,shape⟩
  intro value member
  rw [shape] at member
  simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;> assumption
#print axioms accepted
end AspisR1.NFC_FourDomain
end
