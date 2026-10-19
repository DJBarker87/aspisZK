import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Dedup
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
namespace AspisR1.FiniteListCandidateMerge

variable {I M : Type} [Fintype I] [DecidableEq I] [DecidableEq M]

/-- Update one lane, retain the caller's computable joint-distance test,
and remove duplicates without choosing an ordering of a quotient multiset. -/
def advance (keep : Finset I → (I → M) → Bool) (S : Finset I) (lane : I)
    (family : List (I → M)) (decoded : List M) : List (I → M) :=
  ((family.flatMap fun t => decoded.map (Function.update t lane)).filter
    (keep (insert lane S))).dedup

def advanceSpec (keep : Finset I → (I → M) → Bool) (S : Finset I) (lane : I)
    (family : Finset (I → M)) (decoded : Finset M) : Finset (I → M) :=
  ((family.product decoded).image (fun p => Function.update p.1 lane p.2)).filter
    (fun t => keep (insert lane S) t)

theorem advance_toFinset (keep : Finset I → (I → M) → Bool)
    (S : Finset I) (lane : I) (family : List (I → M)) (decoded : List M) :
    (advance keep S lane family decoded).toFinset =
      advanceSpec keep S lane family.toFinset decoded.toFinset := by
  ext t
  simp only [advance, advanceSpec, List.mem_toFinset, List.mem_dedup,
    List.mem_filter, List.mem_flatMap, List.mem_map,
    Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, ha, b, hb, he⟩, hk⟩
    refine ⟨⟨(a,b), ?_, he⟩, hk⟩
    exact Finset.mem_product.mpr
      ⟨List.mem_toFinset.mpr ha, List.mem_toFinset.mpr hb⟩
  · rintro ⟨⟨p, hp, he⟩, hk⟩
    rcases Finset.mem_product.mp hp with ⟨ha,hb⟩
    exact ⟨⟨p.1,List.mem_toFinset.mp ha,p.2,List.mem_toFinset.mp hb,he⟩,hk⟩

def run (keep : Finset I → (I → M) → Bool)
    (decoded : I → List M) (S : Finset I) (family : List (I → M)) :
    List I → List (I → M)
  | [] => family
  | lane :: rest => run keep decoded (insert lane S)
      (advance keep S lane family (decoded lane)) rest

def runSpec (keep : Finset I → (I → M) → Bool)
    (decoded : I → Finset M) (S : Finset I) (family : Finset (I → M)) :
    List I → Finset (I → M)
  | [] => family
  | lane :: rest => runSpec keep decoded (insert lane S)
      (advanceSpec keep S lane family (decoded lane)) rest

theorem run_toFinset (keep : Finset I → (I → M) → Bool)
    (decoded : I → List M) (lanes : List I)
    (S : Finset I) (family : List (I → M)) :
    (run keep decoded S family lanes).toFinset =
      runSpec keep (fun i => (decoded i).toFinset) S family.toFinset lanes := by
  induction lanes generalizing S family with
  | nil => rfl
  | cons lane rest ih =>
    simp only [run, runSpec]
    rw [ih, advance_toFinset]

theorem run_nodup (keep : Finset I → (I → M) → Bool)
    (decoded : I → List M) (lanes : List I)
    (S : Finset I) (family : List (I → M)) (hf : family.Nodup) :
    (run keep decoded S family lanes).Nodup := by
  induction lanes generalizing S family with
  | nil => exact hf
  | cons lane rest ih =>
    apply ih
    exact List.nodup_dedup _

/-- Any retained finite-set cardinal bound is now a bound on the actual
list length, since deduplication is part of every update. -/
theorem run_length_le (keep : Finset I → (I → M) → Bool)
    (decoded : I → List M) (lanes : List I)
    (S : Finset I) (family : List (I → M)) (hf : family.Nodup)
    (bound : Nat)
    (hbound : (runSpec keep (fun i => (decoded i).toFinset)
      S family.toFinset lanes).card ≤ bound) :
    (run keep decoded S family lanes).length ≤ bound := by
  rw [← run_toFinset] at hbound
  simpa only [List.toFinset_card_of_nodup (run_nodup keep decoded lanes S family hf)]
    using hbound

#print axioms advance
#print axioms run
#print axioms advance_toFinset
#print axioms run_toFinset
#print axioms run_nodup
#print axioms run_length_le
end AspisR1.FiniteListCandidateMerge
