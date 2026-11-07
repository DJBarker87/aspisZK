import NNG_LIBClaimsDomain
import NNG_FromFnValues136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SelectedMaskCanonical
open Aeneas Aeneas.Std NNG_Emitted NNG_Array136 NNG_LIBScalar NNG_LIBArrayDomain NNG_LIBClaimsDomain

theorem cell (claims : Claims) (domain : DomainClaims claims) (i : Usize) (hi : i.val<29) :
    Domain (NNG_Array136.cell claims i hi) := by
  have row : DomainArray (row0 claims) := by
    apply domain
    unfold row0 NNG_Array136.get
    exact List.getElem_mem _
  exact get_domain (row0 claims) row i hi
#print axioms cell

theorem low (claims : Claims) (domain : DomainClaims claims) : DomainArray (NNG_FromFnValues136.low claims) := by
  intro q member
  obtain ⟨i,visited,same⟩ := List.mem_map.mp member
  subst q
  have bound : i.val<16 := NNG_FromFnOn136.indices_bound 16#usize i visited
  rw [NNG_FromFnValues136.firstValue,dif_pos bound]
  exact cell claims domain i (by omega)
#print axioms low

theorem high (claims : Claims) (domain : DomainClaims claims) : DomainArray (NNG_FromFnValues136.high claims) := by
  intro q member
  obtain ⟨i,visited,same⟩ := List.mem_map.mp member
  subst q
  have bound : i.val<10 := NNG_FromFnOn136.indices_bound 10#usize i visited
  rw [NNG_FromFnValues136.secondValue,dif_pos bound]
  exact cell claims domain (NNG_Offset16.shifted i) (NNG_Offset16.bound i bound)
#print axioms high
end AspisR1.NNG_SelectedMaskCanonical
