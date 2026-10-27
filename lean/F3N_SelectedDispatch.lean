import F3N_SelectedScalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_SelectedDispatch
open Aeneas Aeneas.Std Result
open AspisR1ClaimPreparedBridge
open AspisR1PublicPreparation
open AspisR1CurrentPreparedClaim

theorem selected {Hash : Type} (sem : AspisR1PublicPreparation.r1_semantic.Verified Hash) (y1 : Slice U8)
    (Y : Fin 6 → Fin 29 → AspisWideTower.WideExact)
    (claims : ∀ (point l : Usize) (hp : point.val<3) (hl : l.val<29) row scalar,
      Array.index_usize sem.claims point=ok row → Array.index_usize row l=ok scalar →
      LiteralOpeningView.eK (F3L_RhoMeaning.decode scalar)=Y ⟨point.val,by omega⟩ ⟨l.val,hl⟩)
    (extra : ∀ (l : Usize) (hl : l.val<29) scalar,
      Array.index_usize sem.extra l=ok scalar →
      LiteralOpeningView.eK (F3L_RhoMeaning.decode scalar)=Y 3 ⟨l.val,hl⟩)
    (before : ∀ (l : Usize) (hl : l.val<29) scalar,
      Array.index_usize sem.before_z1 l=ok scalar →
      LiteralOpeningView.eK (F3L_RhoMeaning.decode scalar)=Y 4 ⟨l.val,hl⟩)
    (final : ∀ (l : Usize) (hl : l.val<29) parsed,
      ClaimParser.field y1 l=ok parsed → AspisR1CurrentPreparedClaim.Concrete.Canonical parsed →
      LiteralOpeningView.eK (F3L_RhoMeaning.decode (fromClaimQ parsed.c0))=Y 5 ⟨l.val,hl⟩)
    (point l : Usize) (hp : point.val<6) (hl : l.val<29)
    (scalar : AspisR1CurrentPreparedClaim.aspis_core.field.QM31)
    (source : PublicSelectedSource sem y1 point l (fromClaimQ scalar)) :
    AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed scalar=Y ⟨point.val,hp⟩ ⟨l.val,hl⟩ := by
  rw [F3N_SelectedScalar.numeric]
  by_cases h2 : point.val<3
  · obtain ⟨row,readRow,readScalar⟩ := source.1 (by change point.val≤2;omega)
    exact claims point l h2 hl row _ readRow readScalar
  · by_cases h3 : point.val=3
    · have pointEq : point=3#usize := UScalar.eq_of_val_eq h3
      subst point
      exact extra l hl _ (source.2.1 rfl)
    · by_cases h4 : point.val=4
      · have pointEq : point=4#usize := UScalar.eq_of_val_eq h4
        subst point
        exact before l hl _ (source.2.2.1 rfl)
      · have pointEq : point=5#usize := UScalar.eq_of_val_eq (by change point.val=5; omega)
        subst point
        obtain ⟨parsed,read,canonical,same⟩ := source.2.2.2 rfl
        rw [same]
        exact final l hl parsed read canonical

#print axioms selected
end AspisR1.F3N_SelectedDispatch
end
