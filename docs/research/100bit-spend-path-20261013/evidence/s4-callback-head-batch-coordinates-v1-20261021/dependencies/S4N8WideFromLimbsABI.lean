import S4OuterN8BatchResidueV2
import EbyKFinishABI

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FastDotsN8WideFromLimbsABI

abbrev U32 := Std.U32
abbrev CurrentWide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev FinishWide := AspisR1EbyKFinish.field.wide_exact.WideExact

/-- Coordinate-preserving map between the two separately generated nominal
    WideExact carriers. -/
def finishToCurrent (x : FinishWide) : CurrentWide :=
  { c0 :=
      { c0 := { a := x.c0.c0.a, b := x.c0.c0.b }
        c1 := { a := x.c0.c1.a, b := x.c0.c1.b } }
    c1 :=
      { c0 := { a := x.c1.c0.a, b := x.c1.c0.b }
        c1 := { a := x.c1.c1.a, b := x.c1.c1.b } } }

/-- Explicit Ops candidate for the current `wideFromLimbs` field: call the
    checked EbyKFinish `from_limbs` body and map its result to the S4 carrier. -/
def finishFromLimbsCurrent (limbs : Array U32 8#usize) :
    Result (Option CurrentWide) := do
  let parsed ← AspisR1EbyKFinish.field.wide_exact.WideExact.from_limbs limbs
  match parsed with
  | none => ok none
  | some value => ok (some (finishToCurrent value))

/-- Concrete installed operation adapter. Its semantic relationship to the
    frozen current-source operation is the separately recorded byte/ABI
    correspondence; the Lean operation itself is explicit and checked. -/
def withCurrentFromLimbs (ops : AspisR1FastDotsCurrent.FourDotsOps) :
    AspisR1FastDotsCurrent.FourDotsOps :=
  { ops with wideFromLimbs := finishFromLimbsCurrent }

theorem withCurrentFromLimbs_binding
    (ops : AspisR1FastDotsCurrent.FourDotsOps) (limbs : Array U32 8#usize) :
    (withCurrentFromLimbs ops).wideFromLimbs limbs = finishFromLimbsCurrent limbs := rfl

private theorem xs_length (xs : Array U32 8#usize) : xs.val.length = 8 := by
  have hsize : (8#usize).val = 8 := by scalar_tac
  simpa [hsize] using xs.property

theorem finishFromLimbsCurrent_make (a b c d e f g h : U32)
    (Ca : a.val < AspisV8R17.RawReducer.P)
    (Cb : b.val < AspisV8R17.RawReducer.P)
    (Cc : c.val < AspisV8R17.RawReducer.P)
    (Cd : d.val < AspisV8R17.RawReducer.P)
    (Ce : e.val < AspisV8R17.RawReducer.P)
    (Cf : f.val < AspisV8R17.RawReducer.P)
    (Cg : g.val < AspisV8R17.RawReducer.P)
    (Ch : h.val < AspisV8R17.RawReducer.P) :
    finishFromLimbsCurrent (Array.make 8#usize [a,b,c,d,e,f,g,h]) =
      .ok (some (finishToCurrent
        (AspisR1EbyKFinish.Proof.wideFromParts a b c d e f g h))) := by
  unfold finishFromLimbsCurrent
  rw [AspisR1EbyKFinish.Proof.canonical_from_limbs
    a b c d e f g h Ca Cb Cc Cd Ce Cf Cg Ch]
  rfl

private def word0 (xs : Array U32 8#usize) : U32 :=
  xs.val[0]'(by have hx := xs_length xs; omega)
private def word1 (xs : Array U32 8#usize) : U32 :=
  xs.val[1]'(by have hx := xs_length xs; omega)
private def word2 (xs : Array U32 8#usize) : U32 :=
  xs.val[2]'(by have hx := xs_length xs; omega)
private def word3 (xs : Array U32 8#usize) : U32 :=
  xs.val[3]'(by have hx := xs_length xs; omega)
private def word4 (xs : Array U32 8#usize) : U32 :=
  xs.val[4]'(by have hx := xs_length xs; omega)
private def word5 (xs : Array U32 8#usize) : U32 :=
  xs.val[5]'(by have hx := xs_length xs; omega)
private def word6 (xs : Array U32 8#usize) : U32 :=
  xs.val[6]'(by have hx := xs_length xs; omega)
private def word7 (xs : Array U32 8#usize) : U32 :=
  xs.val[7]'(by have hx := xs_length xs; omega)

private theorem array_eq_ordered_make (xs : Array U32 8#usize) :
    xs = Array.make 8#usize
      [word0 xs, word1 xs, word2 xs, word3 xs,
       word4 xs, word5 xs, word6 xs, word7 xs] := by
  have hvals : xs.val = (Array.make 8#usize
      [word0 xs, word1 xs, word2 xs, word3 xs,
       word4 xs, word5 xs, word6 xs, word7 xs]).val := by
    apply List.ext_getElem
    · simp [xs_length xs, Array.make]
    · intro i hi₁ hi₂
      have hi : i < 8 := by
        change i < xs.val.length at hi₁
        have hlen := xs_length xs
        omega
      have hiCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
          i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases hiCases with h | h | h | h | h | h | h | h <;> subst i <;>
        simp [word0, word1, word2, word3, word4, word5, word6, word7, Array.make]
  change (xs : {l : List U32 // l.length = (8#usize).val}) =
    (Array.make 8#usize
      [word0 xs, word1 xs, word2 xs, word3 xs,
       word4 xs, word5 xs, word6 xs, word7 xs] :
       {l : List U32 // l.length = (8#usize).val})
  apply Subtype.ext
  exact hvals

/-- If the explicit S4 operation field is bound to the retained EbyKFinish
    `from_limbs` implementation through the coordinate map, canonical N8
    outputs are accepted and the returned current-carrier value is exactly
    the unchanged limb packing. The Ops binding remains a named premise. -/
theorem actual_wideFromLimbs_of_canonical_words
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (xs : Array U32 8#usize) (out : CurrentWide)
    (hcanonical : ∀ x, x ∈ xs.val → x.val < AspisV8R17.RawReducer.P)
    (hbinding : ∀ limbs, ops.wideFromLimbs limbs = finishFromLimbsCurrent limbs)
    (hcall : ops.wideFromLimbs xs = .ok (some out)) :
    out = finishToCurrent (AspisR1EbyKFinish.Proof.wideFromParts
      (word0 xs) (word1 xs) (word2 xs) (word3 xs)
      (word4 xs) (word5 xs) (word6 xs) (word7 xs)) := by
  have hc0 := hcanonical (word0 xs) (List.getElem_mem (by
    have hx := xs_length xs
    omega))
  have hc1 := hcanonical (word1 xs) (List.getElem_mem (by
    have hx := xs_length xs
    omega))
  have hc2 := hcanonical (word2 xs) (List.getElem_mem (by
    have hx := xs_length xs
    omega))
  have hc3 := hcanonical (word3 xs) (List.getElem_mem (by
    have hx := xs_length xs
    omega))
  have hc4 := hcanonical (word4 xs) (List.getElem_mem (by
    have hx := xs_length xs
    omega))
  have hc5 := hcanonical (word5 xs) (List.getElem_mem (by
    have hx := xs_length xs
    omega))
  have hc6 := hcanonical (word6 xs) (List.getElem_mem (by
    have hx := xs_length xs
    omega))
  have hc7 := hcanonical (word7 xs) (List.getElem_mem (by
    have hx := xs_length xs
    omega))
  have hx := array_eq_ordered_make xs
  have hcall' := hcall
  rw [hbinding xs, hx] at hcall'
  have hmake := finishFromLimbsCurrent_make
    (word0 xs) (word1 xs) (word2 xs) (word3 xs)
    (word4 xs) (word5 xs) (word6 xs) (word7 xs)
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
  have hopt : some out = some (finishToCurrent
      (AspisR1EbyKFinish.Proof.wideFromParts
        (word0 xs) (word1 xs) (word2 xs) (word3 xs)
        (word4 xs) (word5 xs) (word6 xs) (word7 xs))) :=
    Result.ok.inj (hcall'.symm.trans hmake)
  exact Option.some.inj hopt

/-- The installed concrete adapter needs no caller-supplied operation premise. -/
theorem installed_wideFromLimbs_of_canonical_words
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (xs : Array U32 8#usize) (out : CurrentWide)
    (hcanonical : ∀ x, x ∈ xs.val → x.val < AspisV8R17.RawReducer.P)
    (hcall : (withCurrentFromLimbs ops).wideFromLimbs xs = .ok (some out)) :
    out = finishToCurrent (AspisR1EbyKFinish.Proof.wideFromParts
      (word0 xs) (word1 xs) (word2 xs) (word3 xs)
      (word4 xs) (word5 xs) (word6 xs) (word7 xs)) :=
  actual_wideFromLimbs_of_canonical_words (withCurrentFromLimbs ops) xs out hcanonical
    (withCurrentFromLimbs_binding ops) hcall

#print axioms finishFromLimbsCurrent_make
#print axioms actual_wideFromLimbs_of_canonical_words
#print axioms installed_wideFromLimbs_of_canonical_words

end AspisR1FastDotsN8WideFromLimbsABI
