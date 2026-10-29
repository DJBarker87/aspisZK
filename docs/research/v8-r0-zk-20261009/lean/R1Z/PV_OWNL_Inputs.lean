import R1Z.PV_OWNL_HelperRows
import R1Z.PV_OWNL_InputBytes
import R1Z.PV_OWNL_SampleCanon
import R1Z.PV_OWNJ_Points
set_option autoImplicit false
namespace R1Z.PV_OWNL_Inputs
open Aeneas Aeneas.Std
open PV_OWNI_RawOps PV_OWNJ_Points
abbrev Canon := PV_OWNK_TowerCanon.Canon
attribute [local irreducible] PV_B2_FieldValue.aspis_core.field.QM31.add
 PV_B2_FieldValue.aspis_core.field.QM31.mul PV_B2_FieldValue.aspis_core.field.QM31.sub

theorem successorRev_canon (point : List Q) (carry : Q)
 (hp : ∀ q ∈ point, Canon q) (hc : Canon carry) :
 ∀ q ∈ successorRev point carry, Canon q := by
 induction point generalizing carry with
 | nil => intro q hq; simp only [successorRev] at hq; cases hq
 | cons x xs ih =>
  intro q hq
  have hx := hp x (by simp)
  have hm := PV_OWNK_TowerCanon.qm_mul x carry
  simp only [successorRev] at hq
  rcases List.mem_cons.mp hq with rfl | ht
  · exact PV_OWNK_TowerCanon.qm_sub _ _
     (PV_OWNK_TowerCanon.qm_add _ _ hx hc) (PV_OWNK_TowerCanon.qm_add _ _ hm hm)
  · exact ih _ (fun y hy => hp y (List.mem_cons_of_mem _ hy)) hm q ht

theorem zipIdx_fst_mem {A : Type} (xs : List A) (offset : Nat) (e : A × Nat)
 (he : e ∈ xs.zipIdx offset) : e.1 ∈ xs := by
 induction xs generalizing offset with
 | nil => simp at he
 | cons x xs ih =>
  simp only [List.zipIdx_cons,List.mem_cons] at he
  rcases he with rfl | he
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (ih _ he)

theorem statement_points_canon (point : List Q) (hp : ∀ q ∈ point, Canon q) :
 ∀ p ∈ statement_points point, ∀ q ∈ p, Canon q := by
 intro p hmem
 simp only [statement_points,List.mem_cons,List.not_mem_nil,or_false] at hmem
 rcases hmem with rfl | rfl | rfl
 · exact hp
 · intro q hq
   exact successorRev_canon point.reverse one
    (fun x hx => hp x (List.mem_reverse.mp hx)) PV_OWNK_TowerCanon.one_canon q
    (List.mem_reverse.mp hq)
 · intro q hq
   obtain ⟨⟨x,i⟩,hx,rfl⟩ := List.mem_map.mp hq
   have hc := hp x (zipIdx_fst_mem point 0 (x,i) hx)
   change Canon (if i=6 ∨ i=7 then valueSub one x else x)
   by_cases h : i=6 ∨ i=7
   · rw [if_pos h]
     exact PV_OWNK_TowerCanon.qm_sub _ _ PV_OWNK_TowerCanon.one_canon hc
   · rw [if_neg h]
     exact hc

def lift (x : U32) : Q := ⟨⟨x,0#u32⟩,⟨0#u32,0#u32⟩⟩

theorem lift_canon (x : U32) (hx : x.val < 2147483647) : Canon (lift x) := by
 refine ⟨⟨hx,?_⟩,?_,?_⟩ <;> change 0 < 2147483647 <;> omega

theorem columns_canon (base : List (List U32)) (h1 g d : List Q)
 (hb : ∀ c ∈ base, ∀ x ∈ c, x.val < 2147483647)
 (hh : ∀ q ∈ h1, Canon q) (hg : ∀ q ∈ g, Canon q) (hd : ∀ q ∈ d, Canon q) :
 ∀ c ∈ base.map (List.map lift) ++ [h1,g,d], ∀ q ∈ c, Canon q := by
 intro c hc q hq
 rcases List.mem_append.mp hc with hc | hc
 · obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hc
   obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hq
   exact lift_canon x (hb b hb' x hx)
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
   rcases hc with rfl | rfl | rfl
   · exact hh q hq
   · exact hg q hq
   · exact hd q hq
theorem sampled_point (ranks : List (List U32)) :
 ∀ q ∈ ranks.map PV_OWNL_SampleCanon.sample, Canon q := by
 intro q hq
 obtain ⟨rank,_,rfl⟩ := List.mem_map.mp hq
 exact PV_OWNL_SampleCanon.sample_canonical rank

/-- At the accepted-input model: base acceptance, actual helper successful
output, and d/g byte acceptance supply all 29 lanes' canonicality. -/
theorem accepted_columns (base : List (List U32)) (h1 g d : List Q)
 (inverse : Q → Option Q) (chi : Q) (rs : List PV_OWNL_HelperRows.Row)
 (hb : base.all (fun c => c.all (fun x => decide (x.val < 2147483647))) = true)
 (hh : PV_OWNL_HelperRows.vector inverse chi rs = some h1)
 (hg : g.all PV_OWNL_InputBytes.checked = true)
 (hd : d.all PV_OWNL_InputBytes.checked = true) :
 ∀ c ∈ base.map (List.map lift) ++ [h1,g,d], ∀ q ∈ c, Canon q := by
 apply columns_canon base h1 g d
 · intro c hc x hx
   exact of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp hb) c hc)) x hx)
 · exact PV_OWNL_HelperRows.vector_canonical inverse chi rs h1 hh
 · exact PV_OWNL_InputBytes.accepted_canonical g hg
 · exact PV_OWNL_InputBytes.accepted_canonical d hd
#print axioms sampled_point
#print axioms accepted_columns
#print axioms successorRev_canon
#print axioms zipIdx_fst_mem
#print axioms statement_points_canon
#print axioms lift_canon
#print axioms columns_canon
end R1Z.PV_OWNL_Inputs
