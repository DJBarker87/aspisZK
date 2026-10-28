import JHm_Polynomial
import JHm_Weighted5
import JHm_SelectedNumeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_ClaimEvaluation
open Aeneas Aeneas.Std Result
open AspisR1CurrentPreparedClaim Concrete ClaimParts
open JHm_Arithmetic

/-- Evaluates the six actual ordered source dots; all operands remain indexed
by this successful prepared_claim call. -/
theorem source {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (inactive gamma kappa out : E) (g : Array E 29#usize)
    (gc : Canonical gamma) (kc : Canonical kappa) (ic : Canonical inactive)
    (gp : ClaimPowers.powers 29#usize gamma=ok g)
    (call : verifier.prepared_claim JGi_DotOps.ops D sem y1 inactive g kappa=ok (.Ok out))
    (gammaValue : decode gamma=JHm_Arithmetic.gamma)
    (kappaValue : decode kappa=CheckpointBytes5Output.ofE JFq_Kappa.scalar)
    (inactiveValue : decode inactive=0)
    (numeric : ∀ (point j : Usize),point.val<6 → j.val<29 → ∀ q,
      ClaimScalar.SelectedSource sem y1 point j q →
      AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed q=(JHm_Arithmetic.row point.val).getD j.val 0) :
    Canonical out ∧ decode out=CheckpointBytes5Output.ofE JFq_Claim.scalar := by
  obtain ⟨final,zero,dots,oc,oe⟩ := successful_claim_source_gamma_kappa_sum
    D sem y1 inactive gamma kappa out g gc kc ic gp call
  have dot (point : Usize) (hp : point.val<6) :
      decode (final.val[point.val+1]'(by have h:=final.property;change final.val.length=7 at h;omega))=
        JHm_Dots.value point.val := by
    obtain ⟨i,value,hi,xs,inc,cellEq,len,order,reads,decoded⟩ := dots point hp
    have iv := add_one_success_val point i hp inc
    have ce : final.val[point.val+1]'(by have h:=final.property;change final.val.length=7 at h;omega)=value := by
      simpa only [cell,iv] using cellEq
    rw [ce,decoded,gammaValue]
    have total := JHm_Polynomial.ordered_sum xs (fun t => t.1.val)
      (fun t => JHm_Arithmetic.gamma^t.1.val*AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed t.2.2)
      29 len order (fun j => JHm_Arithmetic.gamma^j*(JHm_Arithmetic.row point.val).getD j 0) ?_
    · rw [total,←JHm_Dots.source (⟨point.val,hp⟩ : Fin 6)]
      have hs := JHm_Polynomial.horner_sum JHm_Arithmetic.gamma (JHm_Arithmetic.row point.val)
      rw [JHm_RowFacts.length (⟨point.val,hp⟩ : Fin 6)] at hs
      rw [hs]
      apply Finset.sum_congr rfl
      intro j hj
      rw [List.getD_eq_getElem]
    · intro t ht
      obtain ⟨j,hj,eq⟩ := List.getElem_of_mem ht
      have jt : t.1.val<29 := by rw [←eq,order j hj];omega
      rw [numeric point t.1 hp jt t.2.2 (reads t ht).1]
  refine ⟨oc,?_⟩
  have z : decode (final.val[0]'(by have h:=final.property;change final.val.length=7 at h;omega))=0 := by
    change decode (cell final 0#usize (by decide))=0
    rw [zero,inactiveValue]
  rw [oe]
  unfold kappaPolynomial
  have terms (j : Fin 7) : kappaTerm kappa final j.val=
      if j.val=0 then 0 else JHm_Dots.term (j.val-1) := by
    fin_cases j
    · simp only [kappaTerm,dif_pos (by decide : 0<7),z,mul_zero,if_true]
    · simp only [kappaTerm,dif_pos (by decide),kappaValue]
      rw [dot 0#usize (by decide),JHl_ClaimKappa.numeric (1 : Fin 7)]
      rfl
    · simp only [kappaTerm,dif_pos (by decide),kappaValue]
      rw [dot 1#usize (by decide),JHl_ClaimKappa.numeric (2 : Fin 7)]
      rfl
    · simp only [kappaTerm,dif_pos (by decide),kappaValue]
      rw [dot 2#usize (by decide),JHl_ClaimKappa.numeric (3 : Fin 7)]
      rfl
    · simp only [kappaTerm,dif_pos (by decide),kappaValue]
      rw [dot 3#usize (by decide),JHl_ClaimKappa.numeric (4 : Fin 7)]
      rfl
    · simp only [kappaTerm,dif_pos (by decide),kappaValue]
      rw [dot 4#usize (by decide),JHl_ClaimKappa.numeric (5 : Fin 7)]
      rfl
    · simp only [kappaTerm,dif_pos (by decide),kappaValue]
      rw [dot 5#usize (by decide),JHl_ClaimKappa.numeric (6 : Fin 7)]
      rfl
  have convert : (∑ j∈Finset.range 7,kappaTerm kappa final j)=
      ∑ j∈Finset.range 6,JHm_Dots.term j := by
    rw [Finset.sum_range_succ']
    have zeroTerm := terms (0 : Fin 7)
    simp only [Fin.val_zero,if_true] at zeroTerm
    rw [zeroTerm,add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have h := terms (⟨j+1,by have b:=Finset.mem_range.mp hj;omega⟩ : Fin 7)
    simpa only [Nat.add_ne_zero_iff,or_true,not_false_eq_true,ite_false,Nat.add_sub_cancel] using h
  rw [convert,JHm_Weighted5.source,JHm_Weighted5.retained]
#print axioms source
end AspisR1.JHm_ClaimEvaluation
end
