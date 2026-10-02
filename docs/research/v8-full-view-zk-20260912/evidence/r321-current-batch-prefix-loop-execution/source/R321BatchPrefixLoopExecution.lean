import AspisV8R19.R319BatchPrefixStepExecution

/-! Model-only prefix output for the exact forward-prefix loop. The local
read, prior-last-value, and capacity premises below are explicit invariants;
this file does not prove them for a caller. -/
set_option autoImplicit false
namespace AspisV8R19.R321BatchPrefixLoopExecution

open Aeneas Aeneas.Std Result ControlFlow WP
open AspisV8R15.ExactTowerBase
open AspisV8R19.ComplexBaseExecution (encodeBase)
open AspisV8R19.R319BatchPrefixStepExecution
open AspisR318BatchPrefixRaw.circle_norm.joined_inverse.line_norm.r110_norm

noncomputable section

abbrev VecU32 := alloc.vec.Vec U32
abbrev ListU32 := List U32
abbrev PrefixIter := core.slice.iter.Iter U32

/-- Model-only list of the newly appended forward-prefix values. -/
def prefixValues (f : Nat → M31Exact) : Nat → Nat → M31Exact → ListU32
  | _, 0, _ => []
  | i, n + 1, p =>
      encodeBase (p * f i) :: prefixValues f (i + 1) n (p * f i)

theorem prefixValues_length (f : Nat → M31Exact) (i n : Nat)
    (p : M31Exact) : (prefixValues f i n p).length = n := by
  induction n generalizing i p with
  | zero => simp [prefixValues]
  | succ n ih => simp [prefixValues, ih]

theorem batch_loop0_prefixValues
    (f : Nat → M31Exact) (n : Nat)
    (iter : PrefixIter) (px : VecU32) (p : M31Exact)
    (hremaining : iter.i + n = iter.slice.val.length)
    (hx : ∀ j, iter.i ≤ j → j < iter.slice.val.length →
      iter.slice.val[j]? = some (encodeBase (f j)))
    (hlast : px.val.getLast? = some (encodeBase p))
    (hcap : px.val.length + n ≤ Usize.max) :
    ∃ out : VecU32,
      out.val = px.val ++ prefixValues f iter.i n p ∧
      batch_loop0 iter px = .ok out := by
  induction n generalizing iter px p with
  | zero =>
      refine ⟨px, ?_, ?_⟩
      · simp [prefixValues]
      · rw [batch_loop0, loop.eq_def]
        dsimp only
        have hstop : iter.slice.val.length ≤ iter.i := by omega
        rw [body0_done iter px hstop]
  | succ n ih =>
      have hstep : iter.i < iter.slice.val.length := by omega
      have hreadOpt : iter.slice.val[iter.i]? =
          some (encodeBase (f iter.i)) :=
        hx iter.i (by omega) hstep
      have hread : iter.slice.val[iter.i] = encodeBase (f iter.i) := by
        simpa only [List.getElem?_eq_getElem hstep, Option.some.injEq] using hreadOpt
      have hpushcap : px.val.length < Usize.max := by omega
      obtain ⟨px1, hpushval, hbody⟩ := body0_step iter px (f iter.i) p
        hstep hread hlast hpushcap
      have hlast1 : px1.val.getLast? =
          some (encodeBase (p * f iter.i)) := by
        rw [hpushval]
        simp only [List.getLast?_append_cons, List.getLast?_singleton]
      let iter1 : PrefixIter := {iter with i := iter.i + 1}
      have hremaining1 : iter1.i + n = iter1.slice.val.length := by
        dsimp [iter1]
        omega
      have hx1 : ∀ j, iter1.i ≤ j → j < iter1.slice.val.length →
          iter1.slice.val[j]? = some (encodeBase (f j)) := by
        intro j hlow hup
        exact hx j (by dsimp [iter1] at hlow ⊢; omega)
          (by dsimp [iter1] at hup ⊢; omega)
      have hcap1 : px1.val.length + n ≤ Usize.max := by
        rw [hpushval]
        simp only [List.length_append, List.length_singleton]
        omega
      obtain ⟨out, hout, hloop⟩ := ih iter1 px1 (p * f iter.i)
        hremaining1 hx1 hlast1 hcap1
      refine ⟨out, ?_, ?_⟩
      · calc
          out.val = px1.val ++ prefixValues f iter1.i n (p * f iter.i) := hout
          _ = px.val ++ prefixValues f iter.i (n + 1) p := by
            rw [hpushval]
            dsimp [iter1]
            simp [prefixValues, List.append_assoc]
      · rw [batch_loop0, loop.eq_def]
        dsimp only
        rw [hbody]
        exact hloop

theorem batch_loop1_eq_loop0 (iter : PrefixIter) (px : VecU32) :
    batch_loop1 iter px = batch_loop0 iter px := by
  rfl

#print axioms prefixValues_length
#print axioms batch_loop0_prefixValues
#print axioms batch_loop1_eq_loop0

end
end AspisV8R19.R321BatchPrefixLoopExecution
