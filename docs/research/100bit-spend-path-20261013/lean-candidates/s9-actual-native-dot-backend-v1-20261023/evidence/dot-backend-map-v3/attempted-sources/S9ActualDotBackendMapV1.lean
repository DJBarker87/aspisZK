import S9ActualDotLoopMapV1
import EbyKPushDotBackend
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualDotBackendMapV1
open AspisR1S9ActualDotBodyMapV1 AspisR1S9ActualDotLoopMapV1
abbrev actualRaw := _root_.fast_pairing.canonical.Q.raw
abbrev nativePush := AspisR1S9ProductionPairCutV1.fast_pairing.canonical.Dot.push

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B)
    (out : B) (h : (do let a ← m; f a) = .ok out) :
    ∃ a, m = .ok a ∧ f a = .ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok a => exact ⟨a,rfl,h⟩

theorem native_loop_success_sums (raw : Array U64 4#usize) (self out : NativeDot)
    (h : nativeLoop {start:=0#usize,«end»:=4#usize} self raw = .ok out) :
    out.sums = AspisR1DotPushLocal.Proof.updatedSums self.sums raw := by
  obtain ⟨a,b,c,d,hs⟩ := List.length_eq_four.mp self.sums.property
  obtain ⟨r0,r1,r2,r3,hr⟩ := List.length_eq_four.mp raw.property
  have hs' : self.sums=Array.make 4#usize [a,b,c,d] := Subtype.ext hs
  have hr' : raw=Array.make 4#usize [r0,r1,r2,r3] := Subtype.ext hr
  have known : AspisR1DotPushOriginalRaw.Proof.loop {start:=0#usize,«end»:=4#usize}
      (toOld self) raw = .ok ⟨AspisR1DotPushLocal.Proof.updatedSums self.sums raw⟩ := by
    simpa only [toOld,hs',hr'] using
      AspisR1DotPushOriginalRaw.Proof.loop_eq_updatedSums a b c d r0 r1 r2 r3
  have hm := native_loop_success_to_old raw {start:=0#usize,«end»:=4#usize} self out h
  have he := Result.ok.inj (hm.symm.trans known)
  exact congrArg (fun x : OldDot => x.sums) he

/-- SAME successful current emitted native Dot::push gives the concrete S5
backend call with exactly its returned sums. No accumulator bound, input
canonicality, independent raw call or target success is assumed. -/
theorem native_dot_push_success_backend
    (self out : NativeDot) (left right : Array U32 4#usize)
    (h : nativePush self left right = .ok out) :
    AspisR1EbyKPushDotBackend.dotViaRaw actualRaw ⟨self.sums⟩ left right = .ok ⟨out.sums⟩ := by
  unfold nativePush AspisR1S9ProductionPairCutV1.fast_pairing.canonical.Dot.push at h
  obtain ⟨raw,hraw,hloop⟩ := bind_success _ _ _ h
  have hsums := native_loop_success_sums raw self out hloop
  unfold AspisR1EbyKPushDotBackend.dotViaRaw
  rw [AspisR1DotPushLocal.Proof.push_total_from_raw actualRaw ⟨self.sums⟩ left right raw hraw]
  rw [←hsums]
  rfl

#print axioms native_loop_success_sums
#print axioms native_dot_push_success_backend
end AspisR1S9ActualDotBackendMapV1
