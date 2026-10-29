import R1Z.PV_OWNJ_DecodeFold
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNJ_DecodeWeight
open PV_OWNI_RawOps PV_OWNJ_DecodeFold
variable {K : Type} [Field K]

def step (width pref : Nat) (acc : K × Nat) (coordinate : K) : K × Nat :=
 (acc.1 * (if pref.testBit (width-1-acc.2) then coordinate else 1-coordinate),acc.2+1)

theorem weight (decode : Q → K) (D : Decoder decode) (width pref : Nat)
 (coordinates : List Q) (acc : Q × Nat) (ha : Canon acc.1)
 (hc : ∀ q ∈ coordinates, Canon q) :
 let out := coordinates.foldl (PV_OWNI_WeightTotal.step width pref) acc
 Canon out.1 ∧ (decode out.1,out.2) =
 (coordinates.map decode).foldl (step width pref) (decode acc.1,acc.2) := by
 induction coordinates generalizing acc with
 | nil => exact ⟨ha,rfl⟩
 | cons q qs ih =>
  have hq := hc q (by simp)
  have hs : Canon (if pref.testBit (width-1-acc.2) then q else valueSub one q) ∧
   decode (if pref.testBit (width-1-acc.2) then q else valueSub one q) =
    (if pref.testBit (width-1-acc.2) then decode q else 1-decode q) := by
   cases h:pref.testBit (width-1-acc.2)
   · exact D.sub q hq
   · exact ⟨hq,rfl⟩
  have hm := D.mul acc.1 _ ha hs.1
  have hr := ih (PV_OWNI_WeightTotal.step width pref acc q) hm.1
   (fun x hx => hc x (by simp only [List.mem_cons]; exact Or.inr hx))
  constructor
  · exact hr.1
  · simp only [List.foldl_cons,List.map_cons]
    rw [hr.2]
    congr 1
    change (decode (valueMul acc.1 _),acc.2+1) = _
    rw [hm.2,hs.2]
    rfl

#print axioms weight
end R1Z.PV_OWNJ_DecodeWeight
