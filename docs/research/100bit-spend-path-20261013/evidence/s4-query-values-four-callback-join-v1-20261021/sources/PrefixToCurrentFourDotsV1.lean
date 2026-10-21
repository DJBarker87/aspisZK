import Aeneas
import AspisR1Stage2QueryTailCut.Types
import AspisR1Stage2QueryTailCut.ForwardOps
import AspisR1FastDotsCurrent.FunsOpsV4

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1QueryPrefixToCurrentFourDotsV1

abbrev PrefixCM := AspisR1Stage2QueryTailCut.aspis_core.field.CM31
abbrev PrefixQM := AspisR1Stage2QueryTailCut.aspis_core.field.QM31
abbrev PrefixWide := AspisR1Stage2QueryTailCut.aspis_core.field.WideExact
abbrev CurrentCM := AspisR1FastDotsCurrent.aspis_core.field.CM31
abbrev CurrentQM := AspisR1FastDotsCurrent.aspis_core.field.QM31
abbrev CurrentWide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact

def prefixCMToCurrent (x : PrefixCM) : CurrentCM := ⟨x.a, x.b⟩
def prefixQMToCurrent (x : PrefixQM) : CurrentQM :=
  ⟨prefixCMToCurrent x.c0, prefixCMToCurrent x.c1⟩
def prefixWideToCurrent (x : PrefixWide) : CurrentWide :=
  ⟨prefixQMToCurrent x.c0, prefixQMToCurrent x.c1⟩

def currentCMToPrefix (x : CurrentCM) : PrefixCM := ⟨x.a, x.b⟩
def currentQMToPrefix (x : CurrentQM) : PrefixQM :=
  ⟨currentCMToPrefix x.c0, currentCMToPrefix x.c1⟩
def currentWideToPrefix (x : CurrentWide) : PrefixWide :=
  ⟨currentQMToPrefix x.c0, currentQMToPrefix x.c1⟩

theorem currentCMToPrefix_prefixCMToCurrent (x : PrefixCM) :
    currentCMToPrefix (prefixCMToCurrent x) = x := by cases x <;> rfl
theorem currentQMToPrefix_prefixQMToCurrent (x : PrefixQM) :
    currentQMToPrefix (prefixQMToCurrent x) = x := by
  cases x with | mk c0 c1 => cases c0 with | mk a b => cases c1 with | mk c d => rfl
theorem currentWideToPrefix_prefixWideToCurrent (x : PrefixWide) :
    currentWideToPrefix (prefixWideToCurrent x) = x := by
  cases x with
  | mk c0 c1 =>
    cases c0 with
    | mk c00 c01 =>
      cases c00 with
      | mk a b => cases c01 with | mk c d =>
        cases c1 with
        | mk c10 c11 =>
          cases c10 with
          | mk e f => cases c11 with | mk g h => rfl

def prefixArrayToCurrent {n : Std.Usize} (xs : Array PrefixWide n) : Array CurrentWide n :=
  ⟨xs.val.map prefixWideToCurrent, by simpa only [List.length_map] using xs.property⟩
def currentArrayToPrefix {n : Std.Usize} (xs : Array CurrentWide n) : Array PrefixWide n :=
  ⟨xs.val.map currentWideToPrefix, by simpa only [List.length_map] using xs.property⟩

theorem currentArrayToPrefix_prefixArrayToCurrent (xs : Array PrefixWide 29#usize) :
    currentArrayToPrefix (prefixArrayToCurrent xs) = xs := by
  cases xs with
  | mk values hlen =>
    simp [prefixArrayToCurrent, currentArrayToPrefix, List.map_map,
      Function.comp_def, currentWideToPrefix_prefixWideToCurrent]

abbrev PrefixOpeningOp := AspisR1Stage2QueryTailCut.OpeningOp
abbrev PrefixFourDotsOp := AspisR1Stage2QueryTailCut.FourDotsOp

/-- Typed adapter to the current extracted S4 owner. The only value conversion
    on the input is the fieldwise coordinate map above; the current owner's
    emitted `fast_dots.four_dots` receives this exact mapped array. -/
def currentFourDotsAsPrefix (ops : AspisR1FastDotsCurrent.FourDotsOps) : PrefixFourDotsOp :=
  fun q g => do
    let dots ← AspisR1FastDotsCurrent.fast_dots.four_dots ops q (prefixArrayToCurrent g)
    ok (currentArrayToPrefix dots)

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

/-- A successful prefix adapter call is exactly a successful call to the
    actual S4 `four_dots` owner on the coordinate-mapped original `g`. -/
theorem currentFourDotsAsPrefix_success
  (ops : AspisR1FastDotsCurrent.FourDotsOps) (q : Slice Std.U8)
  (g : Array PrefixWide 29#usize) (out : Array PrefixWide 4#usize)
  (h : currentFourDotsAsPrefix ops q g = .ok out) :
  ∃ dots : Array CurrentWide 4#usize,
    AspisR1FastDotsCurrent.fast_dots.four_dots ops q (prefixArrayToCurrent g) = .ok dots ∧
    out = currentArrayToPrefix dots := by
  unfold currentFourDotsAsPrefix at h
  rcases bind_ok_inv h with ⟨dots, hdots, hmap⟩
  refine ⟨dots, hdots, ?_⟩
  exact (Result.ok.inj hmap).symm

/-- Composed prefix success forwards the identical input `g`, after only the
    explicit coordinate map, to the emitted current S4 `four_dots` owner. The
    opening operation remains an independent caller boundary. -/
theorem query_values_forward_prefix_actual_s4
  (openingOp : PrefixOpeningOp) (ops : AspisR1FastDotsCurrent.FourDotsOps)
  (proof : Slice Std.U8) (p : AspisR1Stage2QueryTailCut.verifier.Prepared)
  (a : AspisR1Stage2QueryTailCut.verifier.Accumulator)
  (g : Array PrefixWide 29#usize)
  (obs : Option (AspisR1Stage2QueryTailCut.verifier.Phase → Result Unit))
  (geometry : AspisR1Stage2QueryTailCut.verifier.QueryGeometry)
  (pending : AspisR1Stage2QueryTailCut.verifier.BatchedWeights)
  (out : core.result.Result
    (Std.Usize × Std.Usize × Slice Std.U8 × Array PrefixWide 4#usize)
    AspisR1Stage2QueryTailCut.verifier.Error)
  (h : AspisR1Stage2QueryTailCut.query_values_forward_prefix_ops
    openingOp (currentFourDotsAsPrefix ops) proof p a g obs geometry pending = .ok out) :
  ∃ (i : Std.U32) (u : Std.Usize) (q : Slice Std.U8)
    (dots : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 4#usize),
    Array.index_usize p.queries a.next = .ok i ∧
    lift (UScalar.cast .Usize i) = .ok u ∧
    openingOp proof a.next = .ok q ∧
    AspisR1FastDotsCurrent.fast_dots.four_dots ops q (prefixArrayToCurrent g) = .ok dots ∧
    out = core.result.Result.Ok (a.next, u, q, currentArrayToPrefix dots) := by
  rcases AspisR1Stage2QueryTailCut.query_values_forward_prefix_ops_success
      openingOp (currentFourDotsAsPrefix ops) proof p a g obs geometry pending out h with
    ⟨i, u, q, dotsPrefix, hindex, hu, hopen, hfourPrefix, hout⟩
  rcases currentFourDotsAsPrefix_success ops q g dotsPrefix hfourPrefix with
    ⟨dots, hfourCurrent, hconverted⟩
  refine ⟨i, u, q, dots, hindex, hu, hopen, hfourCurrent, ?_⟩
  simpa only [hconverted] using hout

theorem prefix_entry_coordinates_preserved (x : PrefixWide) :
    (prefixWideToCurrent x).c0.c0.a = x.c0.c0.a ∧
    (prefixWideToCurrent x).c0.c0.b = x.c0.c0.b ∧
    (prefixWideToCurrent x).c0.c1.a = x.c0.c1.a ∧
    (prefixWideToCurrent x).c0.c1.b = x.c0.c1.b ∧
    (prefixWideToCurrent x).c1.c0.a = x.c1.c0.a ∧
    (prefixWideToCurrent x).c1.c0.b = x.c1.c0.b ∧
    (prefixWideToCurrent x).c1.c1.a = x.c1.c1.a ∧
    (prefixWideToCurrent x).c1.c1.b = x.c1.c1.b := by
  cases x with
  | mk c0 c1 =>
    cases c0 with
    | mk c00 c01 =>
      cases c00 with
      | mk a b => cases c01 with | mk c d =>
        cases c1 with
        | mk c10 c11 =>
          cases c10 with
          | mk e f => cases c11 with | mk g h => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms currentFourDotsAsPrefix_success
#print axioms query_values_forward_prefix_actual_s4
#print axioms currentArrayToPrefix_prefixArrayToCurrent
#print axioms prefix_entry_coordinates_preserved

end AspisR1QueryPrefixToCurrentFourDotsV1
