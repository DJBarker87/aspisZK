import R1Z.PV_RunJoin_SemanticLengths40
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SemanticDomainBound66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_SemanticDomain40
variable [ExternalTypes]
theorem after_value (logical : Slice U8) (at1 size : Usize)
    (bound : at1.val+5+size.val≤logical.length) :
    (after at1 size).val=at1.val+5+size.val := by
  have cap : logical.length≤Usize.max := logical.property
  have inc : (Usize.wrapping_add at1 5#usize).val=at1.val+5 :=
    PV_RunJoin_CompactStep39.offset at1 5#usize (by change at1.val+5≤Usize.max;omega)
  unfold after
  rw [PV_RunJoin_CompactStep39.offset _ size (by rw [inc];omega),inc]
theorem complete (ops : ExternalFuns) (logical : Slice U8) (count : U8)
    (at1 : Usize) (row : U8) (records : List (List U8))
    (domain : Domain ops logical count at1 row records) :
    at1.val+records.flatten.length≤logical.length := by
  induction domain with
  | nil at1 row stop last =>
    have h := congrArg UScalar.val last
    simpa only [List.flatten_nil,List.length_nil,Nat.add_zero] using Nat.le_of_eq h
  | copy at1 size row tag rest more shape small bound tail ih =>
    have cursor := after_value logical at1 size bound
    have len := PV_RunJoin_SemanticLengths40.raw logical at1 size bound
    simp only [List.flatten_cons,List.length_append]
    omega
  | compact at1 size row tag n rest more shape large sizeval bound zero tail ih =>
    have cursor := after_value logical at1 size bound
    have len := PV_RunJoin_SemanticLengths40.compact logical at1 size n sizeval bound
    simp only [List.flatten_cons,List.length_append]
    omega
#print axioms after_value
#print axioms complete
end R1Z.PV_RunJoin_SemanticDomainBound66
