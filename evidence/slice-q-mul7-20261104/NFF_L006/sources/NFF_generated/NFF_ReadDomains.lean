import NFF_LoggedEight
import NEV_DotInputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFF_ReadDomains
open Aeneas Aeneas.Std Result

theorem canonical (coefficient : Array U32 8#usize)
    (domain : ∀ word∈coefficient.val,word.val<NEG_DotDomain.P) :
    NFF_LoggedEight.ReadCanonical coefficient := by
  intro index word run
  by_cases inside : index.val<coefficient.val.length
  · obtain ⟨actual,read,point⟩:=WP.spec_imp_exists
      (Array.index_usize_spec coefficient index inside)
    have same : actual=word := Result.ok.inj (read.symm.trans run)
    apply domain word
    rw [←same,point]
    exact List.getElem_mem _
  · change (match coefficient.val[index.val]? with
      | none => fail Error.arrayOutOfBounds | some x => ok x)=ok word at run
    simp [Nat.not_lt.mp inside] at run

/-- The coefficient-domain predicate used by native log replay is obtained
from the SAME actual g selection and projection. -/
theorem selected (g : NEV_DotInputs.Coefficients) (domain : NEV_DotInputs.Canonical g)
    (term : Usize) (inside : term.val<26) :
    ∃ value coefficient,
      Array.index_usize g term=ok value ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs value=ok coefficient ∧
      NFF_LoggedEight.ReadCanonical coefficient := by
  obtain ⟨value,read,_⟩:=WP.spec_imp_exists
    (Array.index_usize_spec g term (by change term.val<g.val.length;rw [g.property];change term.val<29;omega))
  have c:=NEV_DotInputs.selected g domain term (by omega) value read
  obtain ⟨coefficient,project,words⟩:=NEV_DotInputs.limbs value c
  exact ⟨value,coefficient,read,project,canonical coefficient words⟩

#print axioms canonical
#print axioms selected
end AspisR1.NFF_ReadDomains
end
