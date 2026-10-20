import AspisR1RhoResumeInlined.Funs
import CuSavingsRhoResumeLoans
import CuSavingsRhoReader
import CuSavingsLoopInvariant

set_option autoImplicit false
namespace AspisR1.CuSavingsRhoResumeCanonical
open Aeneas Aeneas.Std Result ControlFlow AspisR1CuRho
open CuSavingsRhoInitRow CuSavingsRhoResumeLoans
abbrev State := It × (It → It) × Usize
abbrev Out := Usize × Option (core.result.Result ((alloc.vec.Vec field.QM31) × verifier.Reader) verifier.Error) × It
abbrev body := AspisR1RhoResumeInlined.verifier.resume_weights_loop.body
abbrev sourceLoop := AspisR1RhoResumeInlined.verifier.resume_weights_loop

def Invariant (size : Nat) (state : State) : Prop :=
  state.1.slice.val.length=size ∧ state.1.i≤size ∧ BackGood state.2.1 state.1.i size

def Post (size : Nat) (out : Out) : Prop :=
  match out.2.1 with
  | none => out.2.2.slice.val.length=size ∧ CanonicalFrom out.2.2.slice 0
  | some (.Err _) => True
  | some (.Ok _) => False

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let x ← m;f x) = .ok out) :
    ∃ x,m = .ok x ∧ f x = .ok out := by
  cases m with
  | fail error => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem body_good (size : Nat) (bytes : Slice U8) (iter : It) (back : It → It) (offset : Usize)
    (hinv : Invariant size (iter,back,offset)) (out : ControlFlow State Out)
    (h : body bytes iter back offset = .ok out) :
    match out with
    | .cont state => Invariant size state
    | .done result => Post size result := by
  have hlen : iter.slice.len.val=iter.slice.val.length := by
    simpa only [Slice.length] using Slice.len_val iter.slice
  have hsize : iter.slice.val.length=size := hinv.1
  have hcursor : iter.i≤size := hinv.2.1
  by_cases hi : iter.i < iter.slice.val.length
  · have hactive : iter.i < iter.slice.len := by simpa only [hlen] using hi
    unfold body AspisR1RhoResumeInlined.verifier.resume_weights_loop.body at h
    simp only [core.slice.iter.IteratorIterMut.next,dif_pos hactive,bind_tc_ok,uncurry_apply_pair] at h
    obtain ⟨nextAt,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨slice,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨converted,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨array,_,h⟩ := bind_ok _ _ _ h
    try simp only [lift,bind_tc_ok] at h
    obtain ⟨parsed,hparse,h⟩ := bind_ok _ _ _ h
    cases parsed with
    | none =>
      simp only [AspisR1RhoResumeInlined.core.option.Option.ok_or,
        AspisR1CuRho.core.option.Option.ok_or,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame] at h
      cases Result.ok.inj h
      trivial
    | some q =>
      have hc := CuSavingsRhoReader.parser_success _ q hparse
      simp only [AspisR1RhoResumeInlined.core.option.Option.ok_or,
        AspisR1CuRho.core.option.Option.ok_or,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch] at h
      cases Result.ok.inj h
      refine ⟨hinv.1,?_,?_⟩
      · change iter.i+1≤size
        have hs := hinv.1
        omega
      · change BackGood (fun tail => back (writeAt iter.i q tail)) (iter.i+1) size
        exact back_write back iter.i size q hinv.2.2 (by have hs:=hinv.1;omega) hc
  · have hstop : ¬ iter.i < iter.slice.len := by simpa only [hlen] using hi
    unfold body AspisR1RhoResumeInlined.verifier.resume_weights_loop.body at h
    simp only [core.slice.iter.IteratorIterMut.next,dif_neg hstop,bind_tc_ok,uncurry_apply_pair] at h
    cases Result.ok.inj h
    have hpos : iter.i=size := by have hs:=hinv.1;have hp:=hinv.2.1;omega
    apply back_done back iter size
    · simpa only [hpos] using hinv.2.2
    · exact hinv.1

theorem loop_success (size : Nat) (iter : It) (back : It → It)
    (bytes : Slice U8) (offset : Usize) (hinv : Invariant size (iter,back,offset))
    (out : Out) (h : sourceLoop iter back bytes offset = .ok out) : Post size out := by
  unfold sourceLoop AspisR1RhoResumeInlined.verifier.resume_weights_loop at h
  exact CuSavingsLoopInvariant.success
    (fun state : State => body bytes state.1 state.2.1 state.2.2)
    (Invariant size) (Post size)
    (by intro state hs control hcontrol;cases control <;> exact body_good size bytes state.1 state.2.1 state.2.2 hs _ hcontrol)
    (iter,back,offset) hinv out h

theorem source_success (weights restored : alloc.vec.Vec field.QM31)
    (reader after : verifier.Reader)
    (h : AspisR1RhoResumeInlined.verifier.resume_weights weights reader =
      .ok (.Ok (restored,after))) :
    restored.val.length=weights.val.length ∧ CanonicalFrom restored 0 ∧
      after.bytes=reader.bytes := by
  let start : It := {slice:=weights,i:=0}
  have hinv : Invariant weights.val.length (start,(fun it => it),reader.«at») := by
    refine ⟨rfl,Nat.zero_le _,?_⟩
    exact back_identity weights.val.length
  unfold AspisR1RhoResumeInlined.verifier.resume_weights at h
  simp only [AspisR1RhoResumeInlined.MutAVec.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,
    alloc.vec.Vec.deref_mut,core.slice.Slice.iter_mut,bind_tc_ok,uncurry_apply_pair] at h
  obtain ⟨last,hloop,h⟩ := bind_ok _ _ _ h
  change sourceLoop start (fun it => it) reader.bytes reader.«at» = .ok last at hloop
  have hpost := loop_success weights.val.length start (fun it => it) reader.bytes reader.«at» hinv last hloop
  rcases last with ⟨position,pending,lastIter⟩
  cases pending with
  | none =>
    change (Result.ok (.Ok (lastIter.slice,{reader with «at»:=position})) :
      Result (core.result.Result ((alloc.vec.Vec field.QM31) × verifier.Reader) verifier.Error)) =
      Result.ok (.Ok (restored,after)) at h
    have heq := core.result.Result.Ok.inj (Result.ok.inj h)
    cases heq
    exact ⟨hpost.1,hpost.2,rfl⟩
  | some returned =>
    cases returned with
    | Err error => cases h
    | Ok pair => exact False.elim hpost

#print axioms source_success
#print axioms body_good
#print axioms loop_success
end AspisR1.CuSavingsRhoResumeCanonical
