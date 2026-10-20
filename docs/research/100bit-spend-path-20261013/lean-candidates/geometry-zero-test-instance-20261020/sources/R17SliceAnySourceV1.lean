import R17QueryValuesWholeBodyStoredV1
import Aeneas.Std.SliceIter

open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false

namespace R17SliceAnySourceV1

/-- The pinned `core::slice::iter::Iter::any` macro body, with Rust mutable
references represented by explicit iterator and FnMut states. This is the
source-shaped Lean function; the accompanying source checker pins it to the
specialized `while let Some(x) = self.next()` implementation in core. -/
def sliceIterAnyBody {I T F : Type}
    (next : I → Result (Option T × I))
    (callMut : F → T → Result (Bool × F))
    (state : I × F) : Result (ControlFlow (I × F) (Bool × I)) := do
  let (item, iter') ← next state.1
  match item with
  | none => .ok (.done (false, iter'))
  | some x =>
    let (hit, f') ← callMut state.2 x
    if hit then .ok (.done (true, iter')) else .ok (.cont (iter', f'))

def sliceIterAny {I T F : Type}
    (next : I → Result (Option T × I))
    (callMut : F → T → Result (Bool × F))
    (iter : I) (f : F) : Result (Bool × I) :=
  loop (sliceIterAnyBody next callMut) (iter, f)

/-- The raw emitted value of `field.M31::ZERO` is `0#u32`. -/
def sourceM31Zero : AspisR1QueryGeometryActual.field.M31 := 0#u32

/-- The exact emitted `PartialEq<M31>::eq` expression used by query closure #3. -/
def sourceM31PartialEq (x y : AspisR1QueryGeometryActual.field.M31) : Result Bool := do
  .ok (x = y)

/-- The exact emitted `FnMut` callback body for `x == M31::ZERO`. -/
def queryZeroCallMut (c : Unit) (x : AspisR1QueryGeometryActual.field.M31) :
    Result (Bool × Unit) := do
  let b ← sourceM31PartialEq x sourceM31Zero
  .ok (b, c)

def queryZeroAny (it : core.slice.iter.Iter AspisR1QueryGeometryActual.field.M31) :
    Result (Bool × core.slice.iter.Iter AspisR1QueryGeometryActual.field.M31) :=
  sliceIterAny Aeneas.Std.core.slice.iter.IteratorSliceIter.next queryZeroCallMut it ()

theorem sourceM31PartialEq_spec (x y : AspisR1QueryGeometryActual.field.M31) :
    sourceM31PartialEq x y = .ok (x = y) := by
  rfl


theorem u32_ne_zero_val {x : Std.U32} (h : x ≠ (0#u32)) : (↑x : Nat) ≠ 0 := by
  intro hz
  apply h
  exact Std.UScalar.val_eq_imp x (0#u32) (by simpa using hz)

theorem queryZeroCallMut_spec (x : AspisR1QueryGeometryActual.field.M31) :
    queryZeroCallMut () x = .ok (x = sourceM31Zero, ()) := by
  rfl

theorem queryZeroAny_false_of_noZero
    (xs : List AspisR1QueryGeometryActual.field.M31)
    (hlen : xs.length ≤ Usize.max)
    (hno : ∀ x, x ∈ xs → x ≠ sourceM31Zero) :
    ∃ it', queryZeroAny ⟨⟨xs, hlen⟩, 0⟩ = .ok (false, it') := by
  have hAll : ∀ it : core.slice.iter.Iter AspisR1QueryGeometryActual.field.M31,
      it.slice.val = xs → it.i ≤ xs.length →
      (∀ j, it.i ≤ j → ∀ (hj : j < xs.length), (↑(xs[j]'hj) : Nat) ≠ 0) →
      queryZeroAny it = .ok (false, {it with i := xs.length}) := by
    intro it
    induction hmeasure : xs.length - it.i using Nat.strong_induction_on generalizing it with
    | h n ih =>
      intro hslice hle htail
      cases it with
      | mk s i =>
        have hs : s = (⟨xs, hlen⟩ : Aeneas.Std.Slice AspisR1QueryGeometryActual.field.M31) := by
          apply Subtype.ext
          exact hslice
        subst s
        let here : core.slice.iter.Iter AspisR1QueryGeometryActual.field.M31 :=
          ⟨⟨xs, hlen⟩, i⟩
        simp [here] at hmeasure hle htail
        by_cases hlt : i < xs.length
        · have hhas : i < here.slice.val.length := by
            simpa [here] using hlt
          let there : core.slice.iter.Iter AspisR1QueryGeometryActual.field.M31 :=
            ⟨⟨xs, hlen⟩, i + 1⟩
          let residual : AspisR1QueryGeometryActual.field.M31 := here.slice[i]
          have hsliceVal : here.slice.val = xs := by
            simpa [here] using hslice
          have hnext : Aeneas.Std.core.slice.iter.IteratorSliceIter.next here =
              .ok (some residual, there) := by
            have hhas' : i < here.slice.val.length := hhas
            simp [Aeneas.Std.core.slice.iter.IteratorSliceIter.next, here, there,
              hhas', residual]
            change here.slice[i] = xs[i]'hlt
            calc
              here.slice[i] = here.slice.val[i]'hhas :=
                Aeneas.Std.Slice.getElem_Nat_eq here.slice i hhas
              _ = xs[i]'hlt := by
                cases hsliceVal
                rfl
          have hresEq : residual = xs[i]'hlt := by
            dsimp [residual]
            calc
              here.slice[i] = here.slice.val[i]'hhas :=
                Aeneas.Std.Slice.getElem_Nat_eq here.slice i hhas
              _ = xs[i]'hlt := by
                cases hsliceVal
                rfl
          have hmem : residual ≠ sourceM31Zero := by
            rw [hresEq]
            exact hno xs[i] (List.getElem_mem hlt)
          have hmemNat : (↑residual : Nat) ≠ 0 := u32_ne_zero_val hmem
          have hcall : queryZeroCallMut () residual = .ok (false, ()) := by
            rw [queryZeroCallMut_spec]
            simpa [sourceM31Zero] using hmemNat
          have hbody : sliceIterAnyBody
              Aeneas.Std.core.slice.iter.IteratorSliceIter.next queryZeroCallMut
              (here, ()) = .ok (.cont (there, ())) := by
            simp [sliceIterAnyBody, hnext, hcall]
          have hstep : queryZeroAny here = queryZeroAny there := by
            unfold queryZeroAny sliceIterAny
            rw [loop.eq_def, hbody]
          rw [hstep]
          have hltMeasure : xs.length - there.i < n := by
            simp [there]
            omega
          have htailThere : ∀ j, there.i ≤ j → ∀ (hj : j < xs.length),
              (↑(xs[j]'hj) : Nat) ≠ 0 := by
            intro j hj1 hj2
            exact htail j (by simp [there] at hj1; omega) hj2
          have hrec := ih (xs.length - there.i) hltMeasure there rfl
            (by simp [there]) (by simp [there]; omega) htailThere
          simpa [there] using hrec
        · have heq : i = xs.length := by omega
          have hbody : sliceIterAnyBody
              Aeneas.Std.core.slice.iter.IteratorSliceIter.next queryZeroCallMut
              (here, ()) = .ok (.done (false, here)) := by
            simp [sliceIterAnyBody, here,
              Aeneas.Std.core.slice.iter.IteratorSliceIter.next, hlt, heq]
          unfold queryZeroAny sliceIterAny
          rw [loop.eq_def, hbody]
          simp [here, heq]
  have hstart := hAll ⟨⟨xs, hlen⟩, 0⟩ rfl (by simp) (by
    intro j hj1 hj2
    exact u32_ne_zero_val (hno xs[j] (List.getElem_mem hj2)))
  exact ⟨{slice := ⟨xs, hlen⟩, i := xs.length}, hstart⟩

/-- Soundness of the false result: a successful false run must consume the
whole slice and every visited M31 word is nonzero. -/
theorem queryZeroAny_false_sound
    (xs : List AspisR1QueryGeometryActual.field.M31)
    (hlen : xs.length ≤ Usize.max)
    (it : core.slice.iter.Iter AspisR1QueryGeometryActual.field.M31)
    (hslice : it.slice.val = xs)
    (hle : it.i ≤ xs.length)
    (it' : core.slice.iter.Iter AspisR1QueryGeometryActual.field.M31)
    (hrun : queryZeroAny it = .ok (false, it')) :
    it'.i = xs.length ∧
      ∀ j, it.i ≤ j → ∀ (hj : j < xs.length), xs[j] ≠ sourceM31Zero := by
  have hSound : ∀ it : core.slice.iter.Iter AspisR1QueryGeometryActual.field.M31,
      it.slice.val = xs → it.i ≤ xs.length →
      ∀ out, queryZeroAny it = .ok (false, out) →
        out.i = xs.length ∧
          ∀ j, it.i ≤ j → ∀ (hj : j < xs.length), xs[j] ≠ sourceM31Zero := by
    intro it
    induction hmeasure : xs.length - it.i using Nat.strong_induction_on generalizing it with
    | h n ih =>
      intro hslice hle out hrun
      cases hIt : it with
      | mk s i =>
        rw [hIt] at hmeasure hslice hle hrun
        have hs : s = (⟨xs, hlen⟩ : Aeneas.Std.Slice AspisR1QueryGeometryActual.field.M31) := by
          apply Subtype.ext
          exact hslice
        subst s
        let here : core.slice.iter.Iter AspisR1QueryGeometryActual.field.M31 :=
          ⟨⟨xs, hlen⟩, i⟩
        simp [here] at hmeasure hle
        by_cases hlt : i < xs.length
        · have hhas : i < here.slice.val.length := by simpa [here] using hlt
          let there : core.slice.iter.Iter AspisR1QueryGeometryActual.field.M31 :=
            ⟨⟨xs, hlen⟩, i + 1⟩
          let residual : AspisR1QueryGeometryActual.field.M31 := here.slice[i]
          have hsliceVal : here.slice.val = xs := by simpa [here] using hslice
          have hnext : Aeneas.Std.core.slice.iter.IteratorSliceIter.next here =
              .ok (some residual, there) := by
            have hhas' : i < here.slice.val.length := hhas
            simp [Aeneas.Std.core.slice.iter.IteratorSliceIter.next, here, there,
              hhas', residual]
            change here.slice[i] = xs[i]'hlt
            calc
              here.slice[i] = here.slice.val[i]'hhas :=
                Aeneas.Std.Slice.getElem_Nat_eq here.slice i hhas
              _ = xs[i]'hlt := by cases hsliceVal; rfl
          have hresEq : residual = xs[i]'hlt := by
            dsimp [residual]
            calc
              here.slice[i] = here.slice.val[i]'hhas :=
                Aeneas.Std.Slice.getElem_Nat_eq here.slice i hhas
              _ = xs[i]'hlt := by cases hsliceVal; rfl
          by_cases hz : xs[i]'hlt = sourceM31Zero
          · have hcall : queryZeroCallMut () residual = .ok (true, ()) := by
              rw [queryZeroCallMut_spec, hresEq]
              simp [hz]
            have hbody : sliceIterAnyBody
                Aeneas.Std.core.slice.iter.IteratorSliceIter.next queryZeroCallMut
                (here, ()) = .ok (.done (true, there)) := by
              simp [sliceIterAnyBody, hnext, hcall]
            have htrue : queryZeroAny here = .ok (true, there) := by
              unfold queryZeroAny sliceIterAny
              rw [loop.eq_def, hbody]
            rw [htrue] at hrun
            cases hrun
          · have hcall : queryZeroCallMut () residual = .ok (false, ()) := by
              rw [queryZeroCallMut_spec, hresEq]
              have hval : (↑(xs[i]'hlt) : Nat) ≠ 0 :=
                u32_ne_zero_val (by simpa [sourceM31Zero] using hz)
              simpa [sourceM31Zero] using hval
            have hbody : sliceIterAnyBody
                Aeneas.Std.core.slice.iter.IteratorSliceIter.next queryZeroCallMut
                (here, ()) = .ok (.cont (there, ())) := by
              simp [sliceIterAnyBody, hnext, hcall]
            have hstep : queryZeroAny here = queryZeroAny there := by
              unfold queryZeroAny sliceIterAny
              rw [loop.eq_def, hbody]
            have hrecRun : queryZeroAny there = .ok (false, out) := by
              rw [← hstep]
              exact hrun
            have hltMeasure : xs.length - there.i < n := by
              simp [there]
              omega
            have hrec := ih (xs.length - there.i) hltMeasure there rfl rfl
              (by simp [there]; omega) out hrecRun
            refine ⟨hrec.1, ?_⟩
            intro j hj1 hj2
            have hj1' : i ≤ j := by simpa using hj1
            by_cases hji : j = i
            · subst j
              exact hz
            · have hjthere : there.i ≤ j := by simp [there]; omega
              exact hrec.2 j hjthere hj2
        · have heq : i = xs.length := by omega
          have hbody : sliceIterAnyBody
              Aeneas.Std.core.slice.iter.IteratorSliceIter.next queryZeroCallMut
              (here, ()) = .ok (.done (false, here)) := by
            simp [sliceIterAnyBody, here,
              Aeneas.Std.core.slice.iter.IteratorSliceIter.next, hlt, heq]
          have hend : queryZeroAny here = .ok (false, here) := by
            unfold queryZeroAny sliceIterAny
            rw [loop.eq_def, hbody]
          rw [hend] at hrun
          injection hrun with hpair
          have hindex : out.i = here.i := congrArg (fun p => p.2.i) hpair |>.symm
          refine ⟨?_, ?_⟩
          · rw [hindex]
            simp [here, heq]
          · intro j hj1 hj2
            have hj1' : i ≤ j := by simpa using hj1
            omega
  exact hSound it hslice hle it' hrun

#print axioms sourceM31PartialEq_spec
#print axioms queryZeroCallMut_spec
#print axioms queryZeroAny_false_of_noZero
#print axioms queryZeroAny_false_sound

end R17SliceAnySourceV1
