import RPz7_F3N_ClaimCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_OriginalClaim
open Aeneas Aeneas.Std Result
open AspisR1CurrentPreparedClaim AspisR1CurrentPreparedClaim.Concrete AspisR1CurrentPreparedClaim.ClaimParts
open AspisR1ClaimPreparedBridge
open scoped BigOperators
attribute [local irreducible] HAdd.hAdd HMul.hMul HPow.hPow Finset.sum decode kappaPolynomial

theorem value {H : Type} (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (y1 : Slice U8) (inactive gamma kappa out : E) (g : Array E 29#usize)
    (meaning : OriginalPayloadClaimMeaning sem y1 inactive gamma kappa out g)
    (Y : Fin 6 → Fin 29 → AspisWideTower.WideExact)
    (selected : ∀ (point l : Usize) (hp : point.val<6) (hl : l.val<29)
      (scalar : aspis_core.field.QM31),
      PublicSelectedSource sem y1 point l (fromClaimQ scalar) →
      AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed scalar=Y ⟨point.val,hp⟩ ⟨l.val,hl⟩) :
    decode out=JointFunctionalBinding.claimedValue Y (decode inactive) (decode gamma) (decode kappa) := by
  obtain ⟨parts,zero,rows,canonical,claim⟩ := meaning
  apply claim.trans
  apply F3N_ClaimPolynomial.polynomial
  · exact congrArg decode zero
  · intro j
    let point := Usize.ofNat j.val (by scalar_tac)
    have hp : point.val<6 := j.isLt
    obtain ⟨i,value,hi,xs,increment,cellEq,length,order,source,numeric⟩ := rows point hp
    have cellTransport := F3N_ClaimCell.successor point i hp increment parts hi
    have actual : parts.val[j.val+1]'(by have h : parts.val.length=7:=parts.property;omega)=value :=
      cellTransport.symm.trans cellEq
    rw [actual,numeric]
    apply F3N_ClaimRowSum.row gamma xs length order
    intro l
    let t := xs[l.val]'(by omega)
    have member : t∈xs := List.getElem_mem (by omega)
    have ht : t.1.val=l.val := order l.val (by omega)
    have result := selected point t.1 hp (by omega) t.2.2 (source t member).1
    have pj : (⟨point.val,hp⟩ : Fin 6)=j := Fin.ext rfl
    have lj : (⟨t.1.val,by omega⟩ : Fin 29)=l := Fin.ext ht
    rw [pj,lj] at result
    exact result

#print axioms value
end AspisR1.F3N_OriginalClaim
end
