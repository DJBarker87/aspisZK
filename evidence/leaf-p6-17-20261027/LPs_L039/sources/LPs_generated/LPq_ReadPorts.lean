import LPq_PointConstruct
import LPq_Decoder
set_option autoImplicit false
namespace AspisR1.LPq_ReadPorts
open Aeneas Aeneas.Std Result LPi_FieldValues LPm_RawPort AspisR1CurrentPreparedClaim

def backQ (q : aspis_core.field.QM31) : NQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def backE (e : Concrete.E) : NE := ⟨backQ e.c0,backQ e.c1⟩
theorem q_roundtrip (q : aspis_core.field.QM31) : qPort (backQ q)=q := rfl
theorem e_roundtrip (e : Concrete.E) : ePort (backE e)=e := rfl

def SemCanonical {H : Type} (sem : r1_semantic.Verified H) : Prop :=
  (∀ row ∈ sem.claims.val, ∀ q ∈ row.val, canonQ (backQ q)) ∧
  (∀ q ∈ sem.extra.val, canonQ (backQ q)) ∧
  (∀ q ∈ sem.before_z1.val, canonQ (backQ q))

def WeightsCanonical (g : Array Concrete.E 29#usize) : Prop :=
  ∀ v ∈ g.val, canonE (backE v)

theorem weights (g : Array Concrete.E 29#usize) (hg : WeightsCanonical g)
    (l : Usize) (hl : l.val<29) :
    ∃ v : NE, canonE v ∧ Array.index_usize g l=ok (ePort v) := by
  have h : l.val<g.val.length := by rw [g.property]; exact hl
  exact ⟨backE g.val[l.val],hg _ (List.getElem_mem h),by
    rw [e_roundtrip]; exact XRy_ArrayRead.read g l hl⟩

/-- Selection ports derived from the SAME semantic arrays, not supplied reads. -/
theorem semantic {H : Type} (sem : r1_semantic.Verified H) (hc : SemCanonical sem)
    (y1 : Slice U8) (point l : Usize) (hp : point.val<5) (hl : l.val<29) :
    ∃ q : NQ, canonQ q ∧ ClaimScalar.read LPm_PointLoop.ops sem y1 point l=ok (qPort q) := by
  by_cases h3 : point.val<3
  · have pr : point.val<sem.claims.val.length := by rw [sem.claims.property]; exact h3
    let row := sem.claims.val[point.val]
    have lr : l.val<row.val.length := by rw [row.property]; exact hl
    refine ⟨backQ row.val[l.val],hc.1 _ (List.getElem_mem pr) _ (List.getElem_mem lr),?_⟩
    rw [q_roundtrip,LPm_SemanticSelections.claims _ _ _ _ _ h3,
      XRy_ArrayRead.read sem.claims point h3,bind_tc_ok]
    exact XRy_ArrayRead.read row l hl
  · by_cases h4 : point.val=3
    · have lr : l.val<sem.extra.val.length := by rw [sem.extra.property]; exact hl
      refine ⟨backQ sem.extra.val[l.val],hc.2.1 _ (List.getElem_mem lr),?_⟩
      rw [q_roundtrip,LPm_SemanticSelections.extra _ _ _ _ _ h4]
      exact XRy_ArrayRead.read sem.extra l hl
    · have h5 : point.val=4 := by omega
      have lr : l.val<sem.before_z1.val.length := by rw [sem.before_z1.property]; exact hl
      refine ⟨backQ sem.before_z1.val[l.val],hc.2.2 _ (List.getElem_mem lr),?_⟩
      rw [q_roundtrip,LPm_SemanticSelections.before_z1 _ _ _ _ _ h5]
      exact XRy_ArrayRead.read sem.before_z1 l hl

theorem five_domains {H : Type} (sem : r1_semantic.Verified H) (hc : SemCanonical sem)
    (y1 : Slice U8) (g : Array Concrete.E 29#usize) (hg : WeightsCanonical g)
    (point : Usize) (hp : point.val<5) : LPq_PointConstruct.ReadDomain sem y1 g point :=
  ⟨fun l hl => semantic sem hc y1 point l hp hl, fun l hl => weights g hg l hl⟩

#print axioms q_roundtrip
#print axioms e_roundtrip
#print axioms weights
#print axioms semantic
#print axioms five_domains
end AspisR1.LPq_ReadPorts
