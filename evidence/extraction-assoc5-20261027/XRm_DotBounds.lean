import XRm_DotAssociation
import XRm_Reduce
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRm_DotBounds
abbrev B : Nat := 17179869184
theorem wrap (n : Nat) : XRk_wrap64 n<18446744073709551616 :=
  Nat.mod_lt _ (by omega)

theorem raw (a b : fast_pairing.canonical.Q) :
    ∀ n ∈ XRk_raw a b, n<18446744073709551616 := by
  intro n member
  unfold XRk_raw at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h
  all_goals subst n; exact wrap _

theorem raw_index (a b : fast_pairing.canonical.Q) (j : Nat) :
    (XRk_raw a b)[j]?.getD 0<18446744073709551616 := by
  cases h : (XRk_raw a b)[j]? with
  | none => simp only [h,Option.getD_none]; omega
  | some n =>
    simp only [h,Option.getD_some]
    exact raw a b n (List.mem_of_getElem? h)

theorem partial_bound (n : Nat) (hn : n<18446744073709551616) : XRk_partial n<B := by
  have fold := XRm_Reduce.mersenneFold31_lt_two34 hn
  change n%2147483648+n/2147483648<B at fold
  unfold XRk_partial XRk_wrap64
  have le := Nat.mod_le (n%2147483648+n/2147483648) 18446744073709551616
  omega

def term (j : Fin 4) (v : XRl_DotSums.Operand) :=
  XRk_partial ((XRk_raw v.1 v.2)[j.val]?.getD 0)
theorem term_bound (j : Fin 4) (v : XRl_DotSums.Operand) : term j v<B :=
  partial_bound _ (raw_index v.1 v.2 j.val)

theorem u64_value (n : Nat) : (XRk_u64 n).val=XRk_wrap64 n := by
  simp [XRk_u64]

theorem step_value (j : Fin 4) (s : U64) (v : XRl_DotSums.Operand)
    (bound : s.val+term j v<18446744073709551616) :
    (XRl_DotSums.cellStep j s v).val=s.val+term j v := by
  rw [XRl_DotSums.cellStep,u64_value]
  exact Nat.mod_eq_of_lt bound
#print axioms wrap
#print axioms raw
#print axioms raw_index
#print axioms partial_bound
#print axioms term_bound
#print axioms u64_value
#print axioms step_value
end XRm_DotBounds
