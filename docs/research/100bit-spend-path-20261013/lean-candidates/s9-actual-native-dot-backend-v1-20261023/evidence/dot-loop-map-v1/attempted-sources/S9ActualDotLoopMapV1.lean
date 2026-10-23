import S9ActualDotBodyMapV1
import S9RangeNextProgressV2
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ActualDotLoopMapV1
open AspisR1S9ActualDotBodyMapV1
open AspisR1S9SourceResultTransportV1 AspisR1S9LoopSuccessTransportV1
abbrev nativeBody := AspisR1S9ProductionPairCutV1.fast_pairing.canonical.Dot.push_loop.body
abbrev nativeLoop := AspisR1S9ProductionPairCutV1.fast_pairing.canonical.Dot.push_loop

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B)
    (out : B) (h : (do let a ← m; f a) = .ok out) :
    ∃ a, m = .ok a ∧ f a = .ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok a => exact ⟨a,rfl,h⟩

theorem native_body_cont_decreases (raw : Array U64 4#usize)
    (iter next : Iter) (self out : NativeDot)
    (h : nativeBody raw iter self = .ok (.cont (next,out))) :
    next.end.val - next.start.val < iter.end.val - iter.start.val := by
  unfold nativeBody AspisR1S9ProductionPairCutV1.fast_pairing.canonical.Dot.push_loop.body at h
  obtain ⟨pair,hnext,h⟩ := bind_success _ _ _ h
  rcases pair with ⟨opt,iterNext⟩
  cases opt with
  | none => cases h
  | some j =>
    simp only [lift,bind_tc_ok] at h
    obtain ⟨x,hx,h⟩ := bind_success _ _ _ h
    obtain ⟨r,hr,h⟩ := bind_success _ _ _ h
    obtain ⟨updated,hupdated,h⟩ := bind_success _ _ _ h
    have hi : iterNext=next := by
      have he : (iterNext, (⟨updated⟩ : NativeDot)) = (next,out) := by injection h
      exact congrArg Prod.fst he
    obtain ⟨hlt,hstart,hend⟩ := AspisR1S9RangeNextProgressV2.range_next_some_progress iter iterNext j hnext
    rw [hi] at hstart hend
    rw [hend]
    omega

/-- One accepted actual raw loop derives the same successful existing S5
source loop with both sums preserved. No target success is assumed. -/
theorem native_loop_success_to_old (raw : Array U64 4#usize)
    (iter : Iter) (self out : NativeDot)
    (h : nativeLoop iter self raw = .ok out) :
    AspisR1DotPushOriginalRaw.Proof.loop iter (toOld self) raw = .ok (toOld out) := by
  exact loop_success_transport
    (fun s : Iter × NativeDot => nativeBody raw s.1 s.2)
    (fun s : Iter × OldDot => AspisR1DotPushOriginalRaw.Proof.body raw s.1 s.2)
    stateToOld toOld (fun s => s.1.end.val-s.1.start.val)
    (fun s => (actual_dot_body_map raw s.1 s.2).symm)
    (fun s next hs => native_body_cont_decreases raw s.1 next.1 s.2 next.2 hs)
    (iter,self) out h

#print axioms native_body_cont_decreases
#print axioms native_loop_success_to_old
end AspisR1S9ActualDotLoopMapV1
