import NDO_JGi_ClaimArrays
import NDO_JGi_ClaimTotal
set_option autoImplicit false
namespace AspisR1.JGi_ClaimRead
open Aeneas Aeneas.Std Result AspisR1ClaimPreparedBridge
open AspisR1CurrentPreparedClaim
open JGi_DotOps (ops CanonQ)

theorem row (a : Array AspisR1PublicPreparation.aspis_core.field.QM31 29#usize)
    (canonical : JGi_ClaimArrays.RowCanonical a) (l : Usize) (hl : l.val<29) :
    ∃ q,Array.index_usize (mapArray toClaimQ a) l=ok q ∧ CanonQ q := by
  obtain ⟨q,call,same⟩ := WP.spec_imp_exists
    (Array.index_usize_spec (mapArray toClaimQ a) l
      (by simp only [Array.length,mapArray,List.length_map,a.property,show (29#usize).val=29 from rfl];exact hl))
  refine ⟨q,call,?_⟩
  rw [same]
  simpa only [mapArray,List.getElem_map] using canonical ⟨l.val,hl⟩
#print axioms row

theorem source {H : Type} (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (y1 : Slice U8)
    (claims : ∀ p : Fin 3,JGi_ClaimArrays.RowCanonical
      (sem.claims.val[p.val]'(by have h:=sem.claims.property;change sem.claims.val.length=3 at h;omega)))
    (extra : JGi_ClaimArrays.RowCanonical sem.extra)
    (before : JGi_ClaimArrays.RowCanonical sem.before_z1)
    (fields : ∀ l : Usize,l.val<29 → ∃ x,ClaimParser.field y1 l=ok x ∧ Concrete.Canonical x)
    (point l : Usize) (hp : point.val<6) (hl : l.val<29) :
    ∃ q,ClaimScalar.read ops (toClaimSem sem) y1 point l=ok q ∧ CanonQ q := by
  by_cases small : point≤2#usize
  · have hp3 : point.val<3 := by scalar_tac
    obtain ⟨a,readA,same⟩ := WP.spec_imp_exists
      (Array.index_usize_spec (toClaimSem sem).claims point
        (by simp only [Array.length,toClaimSem,mapArray,List.length_map,sem.claims.property,show (3#usize).val=3 from rfl];exact hp3))
    have eq : a=mapArray toClaimQ (sem.claims.val[point.val]'(by have h:=sem.claims.property;change sem.claims.val.length=3 at h;omega)) := by
      simpa only [toClaimSem,mapArray,List.getElem_map] using same
    obtain ⟨q,readQ,canonical⟩ := row _ (claims ⟨point.val,hp3⟩) l hl
    refine ⟨q,?_,canonical⟩
    unfold ClaimScalar.read
    rw [if_pos small,readA,bind_tc_ok,eq,readQ]
  · by_cases p3 : point.val=3
    · obtain ⟨q,call,canonical⟩ := row sem.extra extra l hl
      refine ⟨q,?_,canonical⟩
      simp only [ClaimScalar.read,small,if_false,p3,toClaimSem,call]
    · by_cases p4 : point.val=4
      · obtain ⟨q,call,canonical⟩ := row sem.before_z1 before l hl
        refine ⟨q,?_,canonical⟩
        simp only [ClaimScalar.read,small,if_false,p4,toClaimSem,call]
      · have p5 : point.val=5 := by scalar_tac
        obtain ⟨x,call,canonical⟩ := fields l hl
        refine ⟨x.c0,?_,canonical.1⟩
        simp only [ClaimScalar.read,small,if_false,p5]
        change (do let x ← ClaimParser.field y1 l;ClaimParser.c0 x)=ok x.c0
        rw [call,bind_tc_ok]
        rfl
#print axioms source
end AspisR1.JGi_ClaimRead
