import Lean.Elab.Tactic.Simp

namespace RRPartialPrefixCollector

universe u

def collectTotal {K S : Type u} (zeroTest : S → Bool)
    (children : S → List (K × S)) : Nat → S → List (List K)
  | 0, s => if zeroTest s then [[]] else []
  | d+1, s => (children s).flatMap fun (a,t) =>
      (collectTotal zeroTest children d t).map (a :: ·)

def collectChildrenPartial {K S : Type u} (run : S → Option (List (List K))) :
    List (K × S) → Option (List (List K))
  | [] => some []
  | (a,s)::xs => do
      let ys ← run s
      let zs ← collectChildrenPartial run xs
      pure (ys.map (a :: ·) ++ zs)

def collectPartial {K S : Type u} (zeroTest : S → Bool)
    (children? : S → Option (List (K × S))) : Nat → S → Option (List (List K))
  | 0, s => some (if zeroTest s then [[]] else [])
  | d+1, s => do
      let cs ← children? s
      collectChildrenPartial (collectPartial zeroTest children? d) cs

def ready {K S : Type u} (children? : S → Option (List (K × S))) : Nat → S → Prop
  | 0, _ => True
  | d+1, s => ∃ cs, children? s = some cs ∧
      ∀ a t, (a,t) ∈ cs → ready children? d t

theorem collectChildrenPartial_succeeds_of_ready {K S : Type u}
    (run : S → Option (List (List K))) (isReady : S → Prop)
    (hRun : ∀ s, isReady s → ∃ ys, run s = some ys) :
    ∀ xs, (∀ a s, (a,s) ∈ xs → isReady s) →
      ∃ ys, collectChildrenPartial run xs = some ys := by
  intro xs
  induction xs with
  | nil =>
      intro _
      exact ⟨[], rfl⟩
  | cons pair tail ih =>
      rcases pair with ⟨a,s⟩
      intro hready
      have hs : isReady s := hready a s (by simp)
      obtain ⟨ys,hys⟩ := hRun s hs
      obtain ⟨zs,hzs⟩ := ih (by
        intro b t hmem
        exact hready b t (by simp [hmem]))
      exact ⟨ys.map (a :: ·) ++ zs, by simp [collectChildrenPartial, hys, hzs]⟩

theorem collectPartial_succeeds_of_ready {K S : Type u} (zeroTest : S → Bool)
    (children? : S → Option (List (K × S))) :
    ∀ d s, ready children? d s → ∃ xs, collectPartial zeroTest children? d s = some xs := by
  intro d
  induction d with
  | zero =>
      intro s _
      exact ⟨if zeroTest s then [[]] else [], rfl⟩
  | succ d ih =>
      intro s hready
      obtain ⟨cs,hc,hchildren⟩ := hready
      have hwalk : ∃ ys, collectChildrenPartial (collectPartial zeroTest children? d) cs = some ys :=
        collectChildrenPartial_succeeds_of_ready
          (run := collectPartial zeroTest children? d)
          (isReady := ready children? d)
          (hRun := fun t ht => ih t ht)
          (xs := cs) (by
            intro a t hmem
            exact hchildren a t hmem)
      obtain ⟨ys,hys⟩ := hwalk
      exact ⟨ys, by simp [collectPartial, hc, hys]⟩

theorem collectChildrenPartial_success_eq_flatMap {K S : Type u}
    (run : S → Option (List (List K)))
    (total : S → List (List K))
    (hrun : ∀ s ys, run s = some ys → ys = total s) :
    ∀ xs out, collectChildrenPartial run xs = some out →
      out = xs.flatMap fun (a,s) => (total s).map (a :: ·) := by
  intro xs
  induction xs with
  | nil =>
      intro out h
      simp [collectChildrenPartial] at h
      simpa [collectChildrenPartial] using h.symm
  | cons pair tail ih =>
      rcases pair with ⟨a,s⟩
      intro out h
      cases hr : run s with
      | none => simp [collectChildrenPartial, hr] at h
      | some ys =>
          cases ht : collectChildrenPartial run tail with
          | none => simp [collectChildrenPartial, hr, ht] at h
          | some zs =>
              have hys : ys = total s := hrun s ys hr
              have hzs : zs = tail.flatMap fun (b,u) => (total u).map (b :: ·) := ih zs ht
              simp [collectChildrenPartial, hr, ht, hys, hzs, List.flatMap] at h ⊢
              exact h.symm

theorem collectPartial_success_eq_total {K S : Type u} (zeroTest : S → Bool)
    (children? : S → Option (List (K × S))) (children : S → List (K × S))
    (hchildren : ∀ s cs, children? s = some cs → cs = children s) :
    ∀ d s out, collectPartial zeroTest children? d s = some out →
      out = collectTotal zeroTest children d s := by
  intro d
  induction d with
  | zero =>
      intro s out h
      simpa [collectPartial, collectTotal] using (Option.some.inj h).symm
  | succ d ih =>
      intro s out h
      cases hc : children? s with
      | none => simp [collectPartial, hc] at h
      | some cs =>
          have hcs : cs = children s := hchildren s cs hc
          subst cs
          simp only [collectPartial, hc] at h
          have hwalk : collectChildrenPartial (collectPartial zeroTest children? d) (children s) = some out := h
          have htotal := collectChildrenPartial_success_eq_flatMap
            (run := collectPartial zeroTest children? d)
            (total := collectTotal zeroTest children d)
            (hrun := fun t ys hy => ih t ys hy)
            (xs := children s) (out := out) hwalk
          simpa [collectTotal] using htotal

#print axioms collectPartial
#print axioms collectPartial_succeeds_of_ready
#print axioms collectPartial_success_eq_total

end RRPartialPrefixCollector
