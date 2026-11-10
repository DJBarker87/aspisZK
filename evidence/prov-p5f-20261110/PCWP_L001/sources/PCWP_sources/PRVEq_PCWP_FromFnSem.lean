import RPu_FIq_FromFn
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace PCWP_FromFnSem

/-- Left-to-right sequential evaluation of a Result-valued function over a list; the first
non-ok result is the result and later elements are not evaluated (they are never reached). -/
def mapR {α β : Type} (g : α → Result β) : List α → Result (List β)
  | [] => ok []
  | a :: l => do
      let b ← g a
      let bs ← mapR g l
      ok (b :: bs)

section
variable {T F : Type}

/-- The gate's hand model threads state; with a stateless closure it is sequential evaluation. -/
theorem fromFnLoop_stateless (fn : core.ops.function.FnMut F Usize T) (g : Usize → Result T)
    (h : ∀ c i, fn.call_mut c i = (do let x ← g i; ok (x, c))) :
    ∀ (is : List Usize) (c : F),
      AspisR1.OraclePortStdBuilder.fromFnLoop fn is c = (do let xs ← mapR g is; ok (xs, c))
  | [], c => by simp [AspisR1.OraclePortStdBuilder.fromFnLoop, mapR]
  | i :: is, c => by
      have ih := fromFnLoop_stateless fn g h is c
      simp only [AspisR1.OraclePortStdBuilder.fromFnLoop, mapR, h]
      cases hg : g i with
      | ok x => simp [hg, ih]; cases mapR g is <;> simp
      | fail e => simp [hg]
      | div => simp [hg]

/-- All ok: the result list is the pointwise list. -/
theorem mapR_ok {α β : Type} (g : α → Result β) (v : α → β) :
    ∀ (l : List α), (∀ a ∈ l, g a = ok (v a)) → mapR g l = ok (l.map v)
  | [], _ => by simp [mapR]
  | a :: l, h => by
      have ha := h a (by simp)
      have hl := mapR_ok g v l (fun x hx => h x (by simp [hx]))
      simp [mapR, ha, hl]

/-- First failing index decides the result: whatever happens after position k is irrelevant. -/
theorem mapR_fail {α β : Type} (g : α → Result β) (e : Error) :
    ∀ (l : List α) (k : Nat) (hk : k < l.length),
      (∀ j (hj : j < k), ∃ x, g (l[j]'(by omega)) = ok x) → g (l[k]) = fail e →
      mapR g l = fail e
  | [], k, hk, _, _ => by simp at hk
  | a :: l, 0, _, _, h => by simp at h; simp [mapR, h]
  | a :: l, k + 1, hk, hpre, h => by
      obtain ⟨x, hx⟩ := hpre 0 (by omega)
      simp at hx
      have ih := mapR_fail g e l k (by simpa using hk)
        (fun j hj => by have := hpre (j + 1) (by omega); simpa using this) (by simpa using h)
      simp [mapR, hx, ih]

theorem mapR_div {α β : Type} (g : α → Result β) :
    ∀ (l : List α) (k : Nat) (hk : k < l.length),
      (∀ j (hj : j < k), ∃ x, g (l[j]'(by omega)) = ok x) → g (l[k]) = div →
      mapR g l = div
  | [], k, hk, _, _ => by simp at hk
  | a :: l, 0, _, _, h => by simp at h; simp [mapR, h]
  | a :: l, k + 1, hk, hpre, h => by
      obtain ⟨x, hx⟩ := hpre 0 (by omega)
      simp at hx
      have ih := mapR_div g l k (by simpa using hk)
        (fun j hj => by have := hpre (j + 1) (by omega); simpa using this) (by simpa using h)
      simp [mapR, hx, ih]

/-- Spec of the gate's hand model for a stateless closure: it is the length-checked sequential
evaluation over the index list 0..N-1. -/
theorem array_from_fn_copy_stateless (N : Usize) (cp : core.marker.Copy T)
    (fn : core.ops.function.FnMut F Usize T) (d : T) (f : F) (g : Usize → Result T)
    (h : ∀ c i, fn.call_mut c i = (do let x ← g i; ok (x, c))) :
    FIq_Native.array_from_fn_copy N cp fn d f =
      (do let xs ← mapR g (AspisR1.OraclePortStdBuilder.indices N)
          if hl : xs.length = N.val then ok ⟨xs, hl⟩ else .fail .panic) := by
  unfold FIq_Native.array_from_fn_copy AspisR1.OraclePortStdBuilder.fromFn
  rw [fromFnLoop_stateless fn g h]
  cases mapR g (AspisR1.OraclePortStdBuilder.indices N) <;> simp

/-- Element i of the array is f(i): all calls ok. -/
theorem array_from_fn_copy_elem (N : Usize) (cp : core.marker.Copy T)
    (fn : core.ops.function.FnMut F Usize T) (d : T) (f : F) (g : Usize → Result T) (v : Usize → T)
    (h : ∀ c i, fn.call_mut c i = (do let x ← g i; ok (x, c)))
    (hv : ∀ i : Usize, i.val < N.val → g i = ok (v i)) :
    ∃ arr : Array T N, FIq_Native.array_from_fn_copy N cp fn d f = ok arr ∧
      ∀ (k : Nat) (hk : k < N.val),
        arr.val[k]? = some (v (Usize.ofNatCore k (lt_trans hk N.hBounds))) := by
  have hall : ∀ a ∈ AspisR1.OraclePortStdBuilder.indices N, g a = ok (v a) := by
    intro a ha
    simp only [AspisR1.OraclePortStdBuilder.indices, List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact hv _ (by simp [Usize.ofNatCore]; exact i.isLt)
  have hm := mapR_ok g v _ hall
  have hlen : ((AspisR1.OraclePortStdBuilder.indices N).map v).length = N.val := by
    simp [AspisR1.OraclePortStdBuilder.indices]
  refine ⟨⟨(AspisR1.OraclePortStdBuilder.indices N).map v, hlen⟩, ?_, ?_⟩
  · rw [array_from_fn_copy_stateless N cp fn d f g h, hm]; simp [hlen]
  · intro k hk
    simp [AspisR1.OraclePortStdBuilder.indices, hk]

/-- First failing index k decides the result, independent of g at later indices. -/
theorem array_from_fn_copy_first_fail (N : Usize) (cp : core.marker.Copy T)
    (fn : core.ops.function.FnMut F Usize T) (d : T) (f : F) (g : Usize → Result T) (e : Error)
    (h : ∀ c i, fn.call_mut c i = (do let x ← g i; ok (x, c)))
    (k : Nat) (hk : k < N.val)
    (hpre : ∀ j (hj : j < k), ∃ x, g (Usize.ofNatCore j (lt_trans (lt_trans hj hk) N.hBounds)) = ok x)
    (hfail : g (Usize.ofNatCore k (lt_trans hk N.hBounds)) = fail e) :
    FIq_Native.array_from_fn_copy N cp fn d f = fail e := by
  rw [array_from_fn_copy_stateless N cp fn d f g h]
  have hm : mapR g (AspisR1.OraclePortStdBuilder.indices N) = fail e := by
    refine mapR_fail g e _ k (by simpa [AspisR1.OraclePortStdBuilder.indices] using hk) ?_ ?_
    · intro j hj
      obtain ⟨x, hx⟩ := hpre j hj
      exact ⟨x, by simpa [AspisR1.OraclePortStdBuilder.indices] using hx⟩
    · simpa [AspisR1.OraclePortStdBuilder.indices] using hfail
  rw [hm]; rfl

theorem array_from_fn_copy_first_div (N : Usize) (cp : core.marker.Copy T)
    (fn : core.ops.function.FnMut F Usize T) (d : T) (f : F) (g : Usize → Result T)
    (h : ∀ c i, fn.call_mut c i = (do let x ← g i; ok (x, c)))
    (k : Nat) (hk : k < N.val)
    (hpre : ∀ j (hj : j < k), ∃ x, g (Usize.ofNatCore j (lt_trans (lt_trans hj hk) N.hBounds)) = ok x)
    (hdiv : g (Usize.ofNatCore k (lt_trans hk N.hBounds)) = div) :
    FIq_Native.array_from_fn_copy N cp fn d f = div := by
  rw [array_from_fn_copy_stateless N cp fn d f g h]
  have hm : mapR g (AspisR1.OraclePortStdBuilder.indices N) = div := by
    refine mapR_div g _ k (by simpa [AspisR1.OraclePortStdBuilder.indices] using hk) ?_ ?_
    · intro j hj
      obtain ⟨x, hx⟩ := hpre j hj
      exact ⟨x, by simpa [AspisR1.OraclePortStdBuilder.indices] using hx⟩
    · simpa [AspisR1.OraclePortStdBuilder.indices] using hdiv
  rw [hm]; rfl

end
#print axioms fromFnLoop_stateless
#print axioms array_from_fn_copy_stateless
#print axioms array_from_fn_copy_elem
#print axioms array_from_fn_copy_first_fail
#print axioms array_from_fn_copy_first_div
end PCWP_FromFnSem
