import RPu_FJb_MatrixLocality
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_GroupedValues
open FJb_MatrixModel (Values sample block)
def grouped (v : Values) (j : Fin (16#usize).val) : FIv_NativeValue.K :=
  R0P.poseidonMat4 (fun k=>sample v (4*(j.val/4)+k.val))
    ⟨j.val%4,Nat.mod_lt _ (by decide)⟩

theorem inside (v : Values) (g : Nat) (j : Fin (16#usize).val)
    (hg : j.val/4=g) : block v g j=grouped v j := by
  have hj : j.val < 16 := j.isLt
  have hg4 : g < 4 := by omega
  have hm : j.val%4 < (4#usize).val := Nat.mod_lt _ (by decide)
  have hs := FJb_MatrixLocality.sample_same v g hg4 ⟨j.val%4,hm⟩
  have he : 4*g+j.val%4=j.val := by omega
  change sample (block v g) (4*g+j.val%4)=_ at hs
  rw [he] at hs
  simp only [sample,dif_pos j.isLt] at hs
  change block v g j=R0P.poseidonMat4 (fun k=>sample v (4*g+k.val)) ⟨j.val%4,hm⟩ at hs
  simpa only [grouped,hg] using hs

theorem preserved (v : Values) (g : Nat) (j : Fin (16#usize).val)
    (hne : j.val/4≠g) : grouped (block v g) j=grouped v j := by
  have hj : j.val < 16 := j.isLt
  have hg4 : j.val/4 < 4 := by omega
  have he : (fun k : Fin 4=>sample (block v g) (4*(j.val/4)+k.val))=
      (fun k : Fin 4=>sample v (4*(j.val/4)+k.val)) := by
    funext k
    exact FJb_MatrixLocality.sample_other v g (j.val/4) hg4 hne k
  unfold grouped
  rw [he]
#print axioms inside
#print axioms preserved
end AspisR1.FJb_GroupedValues
end
