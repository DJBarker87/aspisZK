import NDO_JHm_Y1Numeric
import NDO_JHm_Row26Numeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_SelectedNumeric
open Aeneas Aeneas.Std Result AspisR1ClaimPreparedBridge
open AspisR1CurrentPreparedClaim
abbrev FE := AspisWideTower.WideExact
abbrev scalar := AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed

theorem get {A : Type} {N : Usize} (a : Array A N) (j : Usize) (hj : j.val<N.val)
    (out : A) (call : Array.index_usize a j=ok out) :
    out=a.val[j.val]'(by simpa only [a.property] using hj) := by
  obtain ⟨q,read,same⟩ := WP.spec_imp_exists
    (Array.index_usize_spec a j (by simpa only [Array.length,a.property] using hj))
  have eq := Result.ok.inj (call.symm.trans read)
  exact eq.trans same
#print axioms get

theorem mapped {N : Usize} (a : Array AspisR1PublicPreparation.aspis_core.field.QM31 N)
    (j : Usize) (hj : j.val<N.val)
    (q : aspis_core.field.QM31) (call : Array.index_usize (mapArray toClaimQ a) j=ok q)
    (values : List FE) (eq : a.val.map JHm_RowFacts.scalar=values) :
    scalar q=values[j.val]'(by rw [←eq,List.length_map,a.property];exact hj) := by
  have hq := get _ j hj q call
  rw [hq]
  simp only [mapArray,List.getElem_map]
  have h := congrArg (fun xs : List FE => xs[j.val]?) eq
  have h1 : j.val<(a.val.map JHm_RowFacts.scalar).length := by
    rw [List.length_map,a.property];exact hj
  have h2 : j.val<values.length := by rw [←eq,List.length_map,a.property];exact hj
  rw [List.getElem?_eq_getElem h1,List.getElem?_eq_getElem h2] at h
  simpa only [List.getElem_map] using Option.some.inj h
#print axioms mapped

theorem source {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (before : Array AspisR1PublicPreparation.aspis_core.field.QM31 29#usize)
    (claims : sem.claims=mapArray (mapArray toClaimQ) JFu_ClaimsData.claims)
    (extra : sem.extra=mapArray toClaimQ JFu_ClaimsData.a3)
    (beforeEq : sem.before_z1=mapArray toClaimQ before)
    (beforeCall : AspisS1ExtractedRoundChildren.decodeMain 29#usize JFu_Q26Source.record 0#usize=ok (.Ok before))
    (payload : y1=JGe_Payload27.value)
    (point j : Usize) (hp : point.val<6) (hj : j.val<29)
    (q : aspis_core.field.QM31) (selected : ClaimScalar.SelectedSource sem y1 point j q) :
    scalar q=(JHm_Arithmetic.row point.val)[j.val]'
      (by rw [JHm_RowFacts.length (⟨point.val,hp⟩ : Fin 6)];exact hj) := by
  interval_cases hv : point.val
  · have same : point=0#usize := UScalar.eq_of_val_eq hv
    subst point
    obtain ⟨a,readA,readQ⟩ := selected.1 (by decide)
    have first : Array.index_usize sem.claims 0#usize=ok (mapArray toClaimQ JFu_ClaimsData.a0) := by
      rw [claims];rfl
    have eq := Result.ok.inj (readA.symm.trans first)
    rw [eq] at readQ
    exact mapped (N:=29#usize) JFu_ClaimsData.a0 j hj q readQ _ JHm_RowFacts.row0
  · have same : point=1#usize := UScalar.eq_of_val_eq hv
    subst point
    obtain ⟨a,readA,readQ⟩ := selected.1 (by decide)
    have first : Array.index_usize sem.claims 1#usize=ok (mapArray toClaimQ JFu_ClaimsData.a1) := by
      rw [claims];rfl
    have eq := Result.ok.inj (readA.symm.trans first)
    rw [eq] at readQ
    exact mapped (N:=29#usize) JFu_ClaimsData.a1 j hj q readQ _ JHm_RowFacts.row1
  · have same : point=2#usize := UScalar.eq_of_val_eq hv
    subst point
    obtain ⟨a,readA,readQ⟩ := selected.1 (by decide)
    have first : Array.index_usize sem.claims 2#usize=ok (mapArray toClaimQ JFu_ClaimsData.a2) := by
      rw [claims];rfl
    have eq := Result.ok.inj (readA.symm.trans first)
    rw [eq] at readQ
    exact mapped (N:=29#usize) JFu_ClaimsData.a2 j hj q readQ _ JHm_RowFacts.row2
  · have same : point=3#usize := UScalar.eq_of_val_eq hv
    subst point
    have readQ := selected.2.1 rfl
    rw [extra] at readQ
    exact mapped (N:=29#usize) JFu_ClaimsData.a3 j hj q readQ _ JHm_RowFacts.row3
  · have same : point=4#usize := UScalar.eq_of_val_eq hv
    subst point
    have readQ := selected.2.2.1 rfl
    rw [beforeEq] at readQ
    exact mapped (N:=29#usize) before j hj q readQ _ (JHm_Row26Numeric.source before beforeCall)
  · have same : point=5#usize := UScalar.eq_of_val_eq hv
    subst point
    obtain ⟨parsed,call,canon,eq⟩ := selected.2.2.2 rfl
    rw [payload] at call
    rw [eq]
    exact JHm_Y1Numeric.source j hj parsed call
#print axioms source
end AspisR1.JHm_SelectedNumeric
end
