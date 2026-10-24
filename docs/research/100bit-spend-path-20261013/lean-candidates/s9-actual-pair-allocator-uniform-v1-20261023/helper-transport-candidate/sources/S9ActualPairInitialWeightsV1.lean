import S9ActualPairOldPrimitiveSuccessV1
import S9ActualPairScalarCallbackV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairInitialWeightsV1
open AspisR1S9ActualPairOldCarrierScalarV1
abbrev GoodArray := AspisR1S9ActualPairScalarCallbackV1.GoodArray
abbrev WC := AspisR1S9ActualPairWideCanonicalV1.Canonical
private theorem index_success_bound {A : Type} {n : Usize}
    (a : Array A n) (i : Usize) (v : A) (h : Array.index_usize a i = .ok v) :
    i.val < n.val := by
  unfold Array.index_usize at h
  cases hopt : a[i]? with
  | none => simp [hopt] at h
  | some y =>
    have hs : a.val[i.val]? = some y := by simpa using hopt
    have hl : i.val < a.val.length := (List.getElem?_eq_some_iff.mp hs).1
    simpa only [a.property] using hl

/-- Reuses the symbolic repeated-array read proof, without expanding four
cells or importing the unrelated constructor arithmetic closure. -/
theorem repeated_native_reads {A : Type} (Can : A → Prop) (n : Usize) (x : A)
    (hx : Can x) :
    ∀ (i : Usize) (v : A), Array.index_usize (Array.repeat n x) i = .ok v → Can v := by
  intro i v hread
  have hi := index_success_bound (Array.repeat n x) i v hread
  have hopt : (Array.repeat n x)[i]? = some x := by
    simp only [Array.getElem?_Usize_eq,Array.repeat]
    simp [hi]
  have hcall : Array.index_usize (Array.repeat n x) i = .ok x := by
    unfold Array.index_usize
    rw [hopt]
  have he : x = v := Result.ok.inj (hcall.symm.trans hread)
  exact he ▸ hx

def initial : Array W 4#usize := Array.repeat 4#usize aspis_core.field.wide_exact.WideExact.ZERO

theorem initial_canonical : GoodArray initial :=
  repeated_native_reads WC 4#usize _ AspisR1S9ActualPairWideOutputCanonicalV1.zero_canonical

theorem initial_maps : mapArray toOldW initial =
    Array.repeat 4#usize AspisR1S9PairCallerStepV1.field.WideExact.ZERO := by
  have hh : mapArray toOldW initial =
      Array.repeat 4#usize (toOldW aspis_core.field.wide_exact.WideExact.ZERO) := by
    apply Subtype.ext
    simp only [initial,AspisR1S9CandidateFoldMapPrimitivesV1.mapArray,Array.repeat,List.map_replicate]
  rw [AspisR1S9ActualPairOldPrimitiveSuccessV1.zero_maps] at hh
  exact hh
#print axioms repeated_native_reads
#print axioms initial_canonical
#print axioms initial_maps
end AspisR1S9ActualPairInitialWeightsV1
