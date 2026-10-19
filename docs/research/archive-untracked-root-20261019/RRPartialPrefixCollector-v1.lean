namespace RRPartialPrefixCollector

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

end RRPartialPrefixCollector
