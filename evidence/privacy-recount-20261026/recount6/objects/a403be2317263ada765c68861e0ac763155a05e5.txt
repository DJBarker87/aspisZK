import R1Z.PV_Join_CanonicalPrimitives5
import R1Z.PV_Join_LoopInvariant5
import R1Z.PV_Join_BindSuccess5
import R1Z.PV_Join_ArrayInvariant5
import R1Z.PV_Join_ProducerCanonical5
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_GAccumulateCanonical5
open Aeneas Aeneas.Std Result ProverRwFull PV_Join_Canonical5 PV_Join_ResultInvariant5
variable [ExternalTypes]
abbrev QA := Array aspis_core.field.QM31 28#usize
abbrev MA := Array aspis_core.field.M31 28#usize
def rank (s : QA × Usize) : Nat := 28-s.2.val
def inv (s : QA × Usize) : Prop := QArray s.1

theorem step (dict : ExternalFuns) (laws : PV_Join_CanonicalPrimitives5.Laws dict) (basis : MA) (scale : aspis_core.field.QM31)
    (out : QA) (k : Usize) (hout : QArray out) :
    Safe (fun cf => match cf with
      | .done ys => QArray ys
      | .cont ys => inv ys ∧ rank ys < rank (out,k))
      (@host_sumcheck.interpolation_accumulate_loop.body _ dict basis scale out k) := by
  unfold host_sumcheck.interpolation_accumulate_loop.body
  split
  · rename_i hk
    intro cf hcf
    obtain ⟨value,hvalue,hcf⟩ := PV_Join_BindSuccess5.unpack _ _ _ hcf
    have hv := PV_Join_ArrayInvariant5.read out hout k value hvalue
    obtain ⟨m,hm,hcf⟩ := PV_Join_BindSuccess5.unpack _ _ _ hcf
    obtain ⟨delta,hd,hcf⟩ := PV_Join_BindSuccess5.unpack _ _ _ hcf
    obtain ⟨d,hd1,hdelta⟩ := laws.scale scale m
    have he : delta=d := Result.ok.inj (hd.symm.trans hd1)
    subst delta
    obtain ⟨next,hn,hcf⟩ := PV_Join_BindSuccess5.unpack _ _ _ hcf
    obtain ⟨n,hn1,hnext⟩ := laws.add value d hv hdelta
    have he : next=n := Result.ok.inj (hn.symm.trans hn1)
    subst next
    obtain ⟨ys,hys,hcf⟩ := PV_Join_BindSuccess5.unpack _ _ _ hcf
    have hy := PV_Join_ArrayInvariant5.update out hout k n hnext ys hys
    simp only [lift,bind_tc_ok] at hcf
    cases hcf
    refine ⟨hy,?_⟩
    have hval : (Std.Usize.wrapping_add k 1#usize).val = k.val+1 := by
      rw [Std.Usize.wrapping_add_val_eq]
      change (k.val+1)%UScalar.size .Usize = k.val+1
      apply Nat.mod_eq_of_lt
      have hbound : k.val<28 := hk
      have big := (28#usize).hSize
      change 28 < UScalar.size .Usize at big
      omega

    change 28-(Std.Usize.wrapping_add k 1#usize).val < 28-k.val
    rw [hval]
    have hbound : k.val<28 := hk
    omega

  · exact PV_Join_ResultInvariant5.ok _ _ hout

#print axioms step
end R1Z.PV_Join_GAccumulateCanonical5
