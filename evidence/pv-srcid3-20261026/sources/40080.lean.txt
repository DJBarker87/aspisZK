import R1Z.PV_Src_PortSumTrace

/-! Checked source-order summation: the exact arithmetic bound prevents
overflow. No wrapping-add replacement or total-effect premise is used. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortSumTotal
open Aeneas Aeneas.Std Result
open PV_Src_PortSumTrace

def natSum (xs : List U64) : Nat := (xs.map (fun x => x.val)).sum

theorem total (xs : List U64) (acc : U64)
    (bound : acc.val + natSum xs < 18446744073709551616) :
    ∃ out, fold xs acc = ok out ∧ out.val = acc.val + natSum xs := by
  induction xs generalizing acc with
  | nil => exact ⟨acc,rfl,by simp only [natSum,List.map_nil,List.sum_nil,Nat.add_zero]⟩
  | cons x xs ih =>
    have hb : acc.val + x.val < 18446744073709551616 := by
      simp only [natSum,List.map_cons,List.sum_cons] at bound
      omega
    have hs : (acc + x : Result U64) ⦃ z => z.val = acc.val + x.val ⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨next,hn,hv⟩ := WP.spec_imp_exists hs
    obtain ⟨out,ho,hov⟩ := ih next (by
      rw [hv]
      simpa only [natSum,List.map_cons,List.sum_cons,Nat.add_assoc] using bound)
    refine ⟨out,?_,?_⟩
    · rw [fold,hn]
      exact ho
    · rw [hov,hv]
      simp only [natSum,List.map_cons,List.sum_cons,Nat.add_assoc]

theorem cast_bound (xs : List U32) :
    natSum (xs.map (UScalar.cast .U64)) ≤ xs.length * 4294967295 := by
  induction xs with
  | nil => simp only [natSum,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons x xs ih =>
    have hx : x.val ≤ 4294967295 := by scalar_tac
    have cast : (UScalar.cast .U64 x).val = x.val := by scalar_tac
    simp only [natSum,List.map_cons,List.sum_cons,List.length_cons] at *
    rw [cast]
    omega

theorem fifteen (xs : List U32) (length : xs.length ≤ 15) :
    ∃ out, fold (xs.map (UScalar.cast .U64)) 0#u64 = ok out ∧
      out.val = natSum (xs.map (UScalar.cast .U64)) := by
  have bound := cast_bound xs
  obtain ⟨out,ho,hv⟩ := total (xs.map (UScalar.cast .U64)) 0#u64 (by
    simp only [UScalar.ofNatCore_val_eq]
    omega)
  exact ⟨out,ho,by simpa only [UScalar.ofNatCore_val_eq,Nat.zero_add] using hv⟩

#print axioms total
#print axioms cast_bound
#print axioms fifteen
end R1Z.PV_Src_PortSumTotal
