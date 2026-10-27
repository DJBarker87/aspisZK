import FJb_ExternalValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_ExternalModel
open FIv_NativeValue (K)
open FJb_MatrixModel (Values sample)
open FJb_GroupedValues (grouped)
def groupRow (v : Values) (g c : Fin 4) : K :=
  R0P.poseidonMat4 (fun k=>v ⟨4*g.val+k.val,by
    have hg := g.isLt
    have hk := k.isLt
    change 4*g.val+k.val < 16
    omega⟩) c

theorem sample_group (v : Values) (g c : Fin 4) :
    sample (grouped v) (4*g.val+c.val)=groupRow v g c := by
  have hg := g.isLt
  have hc := c.isLt
  have hb : 4*g.val+c.val < (16#usize).val := by change 4*g.val+c.val < 16;omega
  let k : Fin (16#usize).val := ⟨4*g.val+c.val,hb⟩
  have hq : k.val/4=g.val := by dsimp only [k];omega
  have hr : (⟨k.val%4,Nat.mod_lt _ (by decide)⟩ : Fin 4)=c := by
    apply Fin.ext
    dsimp only [k]
    omega
  have hi : (fun j : Fin 4=>sample v (4*g.val+j.val))=
      (fun j : Fin 4=>v ⟨4*g.val+j.val,by
        have hj := j.isLt
        change 4*g.val+j.val < 16
        omega⟩) := by
    funext j
    have hj := j.isLt
    have hjb : 4*g.val+j.val < (16#usize).val := by change 4*g.val+j.val < 16;omega
    simp only [sample,dif_pos hjb]
  unfold sample
  rw [dif_pos hb]
  change grouped v k=groupRow v g c
  unfold grouped groupRow
  rw [hq,hr]
  exact congrArg (fun f : Fin 4 → K=>R0P.poseidonMat4 f c) hi

def group (j : Fin (16#usize).val) : Fin 4 := ⟨j.val/4,by
  have hj : j.val < 16 := j.isLt
  omega⟩
def lane (j : Fin (16#usize).val) : Fin 4 := ⟨j.val%4,Nat.mod_lt _ (by decide)⟩

theorem at_index (v : Values) (j : Fin (16#usize).val) :
    grouped v j=groupRow v (group j) (lane j) := by
  have hs := sample_group v (group j) (lane j)
  have hn : 4*(group j).val+(lane j).val=j.val := by
    dsimp only [group,lane]
    omega
  rw [hn] at hs
  have hv : sample (grouped v) j.val=grouped v j := by
    simp only [sample,dif_pos j.isLt]
  exact hv.symm.trans hs

/-- The complete native external layer's symbolic value is the SAME literal
R0P matrix-and-ordered-column-sum model. -/
theorem value (v : Values) : FJb_ExternalValue.model v=R0P.poseidonExternalLinear v := by
  funext j
  have h0 := sample_group v (0 : Fin 4) (lane j)
  have h1 := sample_group v (1 : Fin 4) (lane j)
  have h2 := sample_group v (2 : Fin 4) (lane j)
  have h3 := sample_group v (3 : Fin 4) (lane j)
  change sample (grouped v) (4+(lane j).val)=groupRow v 1 (lane j) at h1
  change sample (grouped v) (8+(lane j).val)=groupRow v 2 (lane j) at h2
  change sample (grouped v) (12+(lane j).val)=groupRow v 3 (lane j) at h3
  have h0' : sample (grouped v) (lane j).val=groupRow v 0 (lane j) := by
    simpa only [show (0 : Fin 4).val=0 from rfl,Nat.mul_zero,Nat.zero_add] using h0
  change grouped v j+
    (sample (grouped v) (lane j).val+sample (grouped v) (4+(lane j).val)+
      sample (grouped v) (8+(lane j).val)+sample (grouped v) (12+(lane j).val))=
    groupRow v (group j) (lane j)+
      ((((0+groupRow v 0 (lane j))+groupRow v 1 (lane j))+groupRow v 2 (lane j))+groupRow v 3 (lane j))
  rw [at_index,h0',h1,h2,h3]
  simp only [zero_add]
#print axioms sample_group
#print axioms at_index
#print axioms value
end AspisR1.FJb_ExternalModel
end
