import S9ActiveFourCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ActiveFourFrameV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9FactorArrayEntryV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Parts := Array W 7#usize
abbrev Libra := Array W 4#usize
abbrev R := core.ops.range.Range Usize

def SameOutside4 (initial final : Parts) : Prop :=
  ∀ (j : Usize) (hj : j.val<7),j.val≠4 → atN final j hj=atN initial j hj

/-- Actual accepted active loop writes only part4. Every other source cell
retains its SAME incoming value, without canonicality/arithmetic meanings. -/
theorem active_success_frame
    (f : Slice U8) (libra : Libra) (iter : R) (initial final : Parts)
    (hloop : weights.Weights.pair_loop8 iter f initial libra=.ok final) :
    SameOutside4 initial final := by
  let step := fun s : R × Parts => weights.Weights.pair_loop8.body f libra s.1 s.2
  let inv := fun s : R × Parts => SameOutside4 initial s.2
  let measure := fun s : R × Parts => s.1.end.val-s.1.start.val
  have hd : ∀ s result,inv s → step s=.ok (.done result) → SameOutside4 initial result := by
    rintro ⟨r,a⟩ result hi hb
    have he := AspisR1S9ActiveFourCanonicalV1.body_done_same f libra r a result hb
    exact he.symm ▸ hi
  have hc : ∀ s s',inv s → step s=.ok (.cont s') → inv s' := by
    rintro ⟨r,a⟩ ⟨r',a'⟩ hi hb
    obtain ⟨j,carry,value,coefficient,product,total,hn,hcarry,hfield,hcf,hm,ha,hu⟩ :=
      AspisR1S9ActiveFourCanonicalV1.body_cont_source f libra r r' a a' hb
    have he := accepted_update_eq_set a 4#usize (by decide) total a' hu
    intro k hk hne
    have hne4 : k.val ≠ (4#usize).val := hne
    rw [he,atN_set a 4#usize k total (by decide) hk,if_neg hne4]
    exact hi k hk hne
  have hm : ∀ s s',step s=.ok (.cont s') → measure s'<measure s := by
    rintro ⟨r,a⟩ ⟨r',a'⟩ hb
    obtain ⟨j,carry,value,coefficient,product,total,hn,hcarry,hfield,hcf,hm,ha,hu⟩ :=
      AspisR1S9ActiveFourCanonicalV1.body_cont_source f libra r r' a a' hb
    obtain ⟨hlt,hj,hstart,hend⟩ :=
      AspisR1S9ConstructorV3Loop2InnerCanonicalV1.next_some_progress r r' j hn
    simp only [measure,hstart,hend]
    omega
  have hinit : inv (iter,initial) := by intro j hj hne; rfl
  have hs : Aeneas.Std.loop step (iter,initial)=.ok final := hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property
    step measure inv (SameOutside4 initial) hd hc hm _ final hinit hs

theorem unshared_active_success_frame
    (f : Slice U8) (libra : Libra) (iter : R) (initial final : Parts)
    (hloop : weights.Weights.pair_loop16 iter f initial libra=.ok final) :
    SameOutside4 initial final := by
  rw [AspisR1S9ActiveFourCanonicalV1.unshared_active_eq] at hloop
  exact active_success_frame f libra iter initial final hloop

/-- SAME inactive-index0 write followed by actual active loop preserves every
real point-part cell (all indices distinct from0 and4). -/
theorem inactive_active_preserves_point_parts
    (f : Slice U8) (libra : Libra) (iter : R) (initial middle final : Parts) (inactive : W)
    (hwrite : Array.update initial 0#usize inactive=.ok middle)
    (hloop : weights.Weights.pair_loop8 iter f middle libra=.ok final) :
    ∀ (j : Usize) (hj : j.val<7),j.val≠0 → j.val≠4 → atN final j hj=atN initial j hj := by
  have hf := active_success_frame f libra iter middle final hloop
  have he := accepted_update_eq_set initial 0#usize (by decide) inactive middle hwrite
  intro j hj hn0 hn4
  have hne0 : j.val ≠ (0#usize).val := hn0
  rw [hf j hj hn4,he,atN_set initial 0#usize j inactive (by decide) hj,if_neg hne0]

#print axioms active_success_frame
#print axioms unshared_active_success_frame
#print axioms inactive_active_preserves_point_parts
end AspisR1S9ActiveFourFrameV1
