import CurrentPreparedSourceMeaning
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge
open AspisR1CurrentPreparedClaim AspisR1CurrentPreparedClaim.Concrete

theorem mapArray_index_success {A B : Type} {N : Usize} (f : A → B)
    (a : Array A N) (i : Usize) (x : A) (h : Array.index_usize a i=ok x) :
    Array.index_usize (mapArray f a) i=ok (f x) := by
  unfold Array.index_usize at h ⊢
  simp only [mapArray,List.getElem?_map]
  cases hr : a.val[i.val]? with
  | none => simp only [hr] at h; cases h
  | some y =>
    simp only [hr] at h ⊢
    cases h
    rfl

theorem mapArray_index_inverse {A B : Type} {N : Usize} (f : A → B) (g : B → A)
    (hinv : ∀ a,g (f a)=a) (a : Array A N) (i : Usize) (x : B)
    (h : Array.index_usize (mapArray f a) i=ok x) :
    Array.index_usize a i=ok (g x) := by
  have hm := mapArray_index_success g (mapArray f a) i x h
  simpa only [mapArray_inverse f g hinv a] using hm

def PublicSelectedSource {H : Type}
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (y1 : Slice U8)
    (point l : Usize) (scalar : PQ) : Prop :=
  (point ≤ 2#usize → ∃ row, Array.index_usize sem.claims point=ok row ∧
    Array.index_usize row l=ok scalar) ∧
  (point=3#usize → Array.index_usize sem.extra l=ok scalar) ∧
  (point=4#usize → Array.index_usize sem.before_z1 l=ok scalar) ∧
  (point=5#usize → ∃ parsed, ClaimParser.field y1 l=ok parsed ∧
    Canonical parsed ∧ scalar=fromClaimQ parsed.c0)

theorem selected_source_original_payload {H : Type}
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (y1 : Slice U8)
    (point l : Usize) (scalar : CQ)
    (h : ClaimScalar.SelectedSource (toClaimSem sem) y1 point l scalar) :
    PublicSelectedSource sem y1 point l (fromClaimQ scalar) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro hp
    obtain ⟨row,hr,hs⟩ := h.1 hp
    refine ⟨mapArray fromClaimQ row,?_,mapArray_index_success fromClaimQ row l scalar hs⟩
    exact mapArray_index_inverse (mapArray toClaimQ) (mapArray fromClaimQ)
      (fun a => mapArray_inverse toClaimQ fromClaimQ from_to_q a) sem.claims point row hr
  · intro hp
    exact mapArray_index_inverse toClaimQ fromClaimQ from_to_q sem.extra l scalar (h.2.1 hp)
  · intro hp
    exact mapArray_index_inverse toClaimQ fromClaimQ from_to_q sem.before_z1 l scalar (h.2.2.1 hp)
  · intro hp
    obtain ⟨parsed,hr,hc,he⟩ := h.2.2.2 hp
    exact ⟨parsed,hr,hc,congrArg fromClaimQ he⟩

#print axioms mapArray_index_success
#print axioms mapArray_index_inverse
#print axioms selected_source_original_payload
end AspisR1ClaimPreparedBridge
