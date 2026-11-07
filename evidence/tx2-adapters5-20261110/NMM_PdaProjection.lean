import NKF_ArrayFrame
set_option autoImplicit false
set_option pp.proofs false
namespace NMM_PdaProjection

theorem bounded_ext {A : Type} (xs ys : List A) (cap : Nat)
 (hx : xs.length ≤ cap) (hy : ys.length ≤ cap)
 (cells : ∀ i, i < cap → xs[i]? = ys[i]?) : xs = ys := by
 apply List.ext_getElem?
 intro i
 by_cases hi : i < cap
 · exact cells i hi
 · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]

structure Args (A : Type) where
 seeds : List (List A)
 program : List A

structure Domain {A : Type} (a : Args A) : Prop where
 seeds : a.seeds.length ≤ 5
 bytes : ∀ (i : Nat) (s : List A), a.seeds[i]? = some s → s.length ≤ 32
 program : a.program.length ≤ 32

structure Window (A : Type) where
 length : Option Nat
 seedByte : Option A
 programByte : Option A

def window {A : Type} (a : Args A) (i j : Nat) : Window A :=
 ⟨(a.seeds[i]?).map List.length,
  (a.seeds[i]?).bind (fun s => s[j]?),a.program[j]?⟩

/-- Every source-ordered PDA argument tuple is recovered from bounded windows.
The actual native prefix association and frame are separate obligations. -/
theorem complete {A : Type} (a b : Args A) (da : Domain a) (db : Domain b)
 (windows : ∀ i, i < 5 → ∀ j, j < 32 → window a i j = window b i j) : a = b := by
  have hs : a.seeds = b.seeds := by
    apply bounded_ext _ _ 5 da.seeds db.seeds
    intro i hi
    have hl := congrArg Window.length (windows i hi 0 (by omega))
    cases ha : a.seeds[i]? with
    | none =>
      cases hb : b.seeds[i]? with
      | none => rfl
      | some ys =>
        simp only [window,ha,hb,Option.map_none,Option.map_some] at hl
        cases hl
    | some xs =>
      cases hb : b.seeds[i]? with
      | none =>
        simp only [window,ha,hb,Option.map_none,Option.map_some] at hl
        cases hl
      | some ys =>
        congr 1
        apply bounded_ext xs ys 32 (da.bytes i xs ha) (db.bytes i ys hb)
        intro j hj
        have h := congrArg Window.seedByte (windows i hi j hj)
        simpa only [window,ha,hb,Option.bind_some] using h
  have hp : a.program = b.program := by
    apply bounded_ext _ _ 32 da.program db.program
    intro j hj
    exact congrArg Window.programByte (windows 0 (by omega) j hj)
  cases a;cases b
  simp only at hs hp
  cases hs;cases hp;rfl

#print bounded_ext
#print axioms bounded_ext
#print complete
#print axioms complete
end NMM_PdaProjection
