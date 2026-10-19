namespace RRPartialPrefixCollector

def collectTotal {K S : Type} (zeroTest : S → Bool)
    (children : S → List (K × S)) : Nat → S → List (List K)
  | 0, s => if zeroTest s then [[]] else []
  | d+1, s => (children s).flatMap fun (a,t) =>
      (collectTotal zeroTest children d t).map (a :: ·)

/-- Bounded prefix enumeration with strict abort on an unavailable root list. -/
def collectPartial {K S : Type} (zeroTest : S → Bool)
    (children? : S → Option (List (K × S))) : Nat → S → Option (List (List K))
  | 0, s => some (if zeroTest s then [[]] else [])
  | d+1, s => do
      let cs ← children? s
      let branches ← cs.mapM fun (a,t) => do
        let ys ← collectPartial zeroTest children? d t
        pure (ys.map (a :: ·))
      pure branches.flatten

theorem partial_eq_some_total {K S : Type} (zeroTest : S → Bool)
    (children? : S → Option (List (K × S))) (children : S → List (K × S))
    (hchildren : ∀ s, children? s = some (children s)) :
    ∀ d s, collectPartial zeroTest children? d s = some (collectTotal zeroTest children d s) := by
  intro d
  induction d with
  | zero => intro s; simp [collectPartial, collectTotal]
  | succ d ih =>
    intro s
    simp only [collectPartial, hchildren s, Option.bind_some]
    rw [List.mapM_eq_mapM]
    simp only [List.mapM_map, Option.mapM_some]
    simp_rw [ih]
    simp [collectTotal, List.flatMap]

end RRPartialPrefixCollector
