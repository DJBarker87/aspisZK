import R1Z.PV_RunJoin_SemanticDomain40
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticLengths40
open Aeneas Aeneas.Std ProverRwFull PV_RunJoin_SemanticDomain40

theorem low (bytes : List U8) (n : Nat) (len : bytes.length=32*n) :
    (PV_RunJoin_SemanticCompact40.low bytes n).length=16*n := by
  have cell : ∀ i : Fin n, ((bytes.drop (32*i.val)).take 16).length=16 := by
    intro i
    rw [List.length_take,List.length_drop,len]
    have := i.isLt
    omega
  simp only [PV_RunJoin_SemanticCompact40.low,List.length_flatten,List.map_map,List.map_ofFn]
  change (List.ofFn (fun i : Fin n => ((bytes.drop (32*i.val)).take 16).length)).sum=16*n
  simp only [cell,List.ofFn_const,List.sum_replicate,smul_eq_mul]
  omega

theorem raw (logical : Slice U8) (at1 size : Usize)
    (bound : at1.val+5+size.val≤logical.length) :
    (PV_RunJoin_SemanticDomain40.raw logical at1 size).length=5+size.val := by
  have hb : at1.val+5+size.val≤logical.val.length := bound
  simp only [PV_RunJoin_SemanticDomain40.raw,List.length_append,List.length_take,List.length_drop]
  omega

theorem compact (logical : Slice U8) (at1 size : Usize) (n : Nat)
    (sizeval : size.val=32*n) (bound : at1.val+5+size.val≤logical.length) :
    (PV_RunJoin_SemanticDomain40.compact logical at1 size n).length=5+16*n := by
  have hb : at1.val+5+size.val≤logical.val.length := bound
  have hs : ((logical.val.drop (at1.val+5)).take size.val).length=32*n := by
    rw [List.length_take,List.length_drop]
    omega
  rw [PV_RunJoin_SemanticDomain40.compact,List.length_append,low _ n hs,
    List.length_take,List.length_drop]
  omega
#print axioms low
#print axioms raw
#print axioms compact
end R1Z.PV_RunJoin_SemanticLengths40
