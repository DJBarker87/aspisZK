import S9IndexedPowersPrefixWriteV1
import S9LoopInvariantPropertyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ActualIndexedPowersSemanticsV1
open AspisR1S9ActualPairWideCanonicalV1
open AspisR1S9ActualIndexedPowersArithmeticV1
open AspisR1S9IndexedPowersPrefixWriteV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
abbrev State := WA × W × Usize

def step (x : W) (s : State) : Result (ControlFlow State WA) :=
  AspisR1S9ProductionPairCutV1.weights.powers_loop.body x s.1 s.2.1 s.2.2

inductive StepTrace (x : W) (a : WA) (p : W) (i : Usize) : ControlFlow State WA → Prop
  | past (hi : ¬i < 4#usize) : StepTrace x a p i (.done a)
  | last (hi : i < 4#usize) (old : W) (back : W → WA)
      (hmut : Array.index_mut_usize a i = .ok (old,back))
      (hlast : Std.Usize.wrapping_add i 1#usize = 4#usize) :
      StepTrace x a p i (.done (back p))
  | more (hi : i < 4#usize) (old : W) (back : W → WA)
      (hmut : Array.index_mut_usize a i = .ok (old,back))
      (hmore : Std.Usize.wrapping_add i 1#usize ≠ 4#usize)
      (p1 : W)
      (hmul : AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.mul p x = .ok p1) :
      StepTrace x a p i (.cont (back p,p1,Std.Usize.wrapping_add i 1#usize))

/-- Every child success and write used below is recovered from the SAME
successful emitted source step. Its last step has no multiplication call. -/
theorem step_success_trace (x : W) (a : WA) (p : W) (i : Usize)
    (flow : ControlFlow State WA) (h : step x (a,p,i) = .ok flow) : StepTrace x a p i flow := by
  unfold step AspisR1S9ProductionPairCutV1.weights.powers_loop.body at h
  split at h
  · rename_i hi
    obtain ⟨pair,hmut,h⟩ := bind_success_inv _ _ _ h
    rcases pair with ⟨old,back⟩
    simp only [lift,bind_tc_ok] at h
    split at h
    · rename_i hlast
      have he := Result.ok.inj h
      subst flow
      exact .last hi old back hmut hlast
    · rename_i hmore
      obtain ⟨p1,hmul,h⟩ := bind_success_inv _ _ _ h
      have he := Result.ok.inj h
      subst flow
      exact .more hi old back hmut hmore p1 hmul
  · rename_i hi
    have he := Result.ok.inj h
    subst flow
    exact .past hi

theorem successor_val (i : Usize) (hi : i.val < 4) :
    (Std.Usize.wrapping_add i 1#usize).val = i.val+1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  have hone : (1#usize : Usize).val = 1 := rfl
  have hb : i.val+1 ≤ UScalar.cMax .Usize := by
    have := Usize.cMax_bound
    scalar_tac
  have hlt := UScalar.bound_suffices .Usize (i.val+1) hb
  rw [hone]
  simp only [UScalar.size]
  exact Nat.mod_eq_of_lt hlt

def Invariant (x : W) (s : State) : Prop :=
  Canonical s.2.1 ∧ decode s.2.1 = decode x ^ s.2.2.val ∧
    Prefix x s.1 s.2.2.val ∧ s.2.2.val ≤ 4

def Output (x : W) (a : WA) : Prop :=
  ∀ (j : Usize) (value : W), Array.index_usize a j = .ok value →
    decode value = decode x ^ j.val

def measure (s : State) : Nat := 4-s.2.2.val

/-- Accepted-run semantic refinement of the actual indexed loop. The invariant
covers the already-written prefix only, so no property of the unwritten
array tail or equality to an older FnMut implementation is assumed. -/
theorem powers_loop_success_semantics (x : W) (hx : Canonical x)
    (a out : WA) (p : W) (i : Usize)
    (hinv : Invariant x (a,p,i))
    (hrun : AspisR1S9ProductionPairCutV1.weights.powers_loop x a p i = .ok out) : Output x out := by
  have hd : ∀ s out, Invariant x s → step x s = .ok (.done out) → Output x out := by
    rintro ⟨a,p,i⟩ out ⟨hp,hpdecode,hprefix,hibound⟩ hbody
    have trace := step_success_trace x a p i (.done out) hbody
    cases trace with
    | past hi =>
      have hiv : i.val = 4 := by
        have hn : ¬i.val < 4 := hi
        omega
      intro j value hread
      have hj := index_success_bound a j value hread
      apply hprefix j value hread
      change j.val < 4 at hj
      omega
    | last hi old back hmut hlast =>
      have hip : i.val < 4 := hi
      have hsucc := successor_val i hip
      have hfinal : (Std.Usize.wrapping_add i 1#usize).val = 4 := congrArg UScalar.val hlast
      have hnext : i.val+1 = 4 := hsucc.symm.trans hfinal
      have hw := write_extends_power_prefix x a i old p back hmut hpdecode hprefix
      intro j value hread
      have hj := index_success_bound (back p) j value hread
      apply hw j value hread
      change j.val < 4 at hj
      omega
  have hc : ∀ s s', Invariant x s → step x s = .ok (.cont s') → Invariant x s' := by
    rintro ⟨a,p,i⟩ s' ⟨hp,hpdecode,hprefix,hibound⟩ hbody
    have trace := step_success_trace x a p i (.cont s') hbody
    cases trace with
    | more hi old back hmut hmore p1 hmul =>
      have hip : i.val < 4 := hi
      have hsucc := successor_val i hip
      have hproduct := mul_success_exact p x p1 hp hx hmul
      refine ⟨hproduct.1,?_,?_,?_⟩
      · change decode p1 = decode x ^ (Std.Usize.wrapping_add i 1#usize).val
        rw [hsucc]
        calc
          decode p1 = decode p * decode x := hproduct.2
          _ = decode x ^ i.val * decode x := by rw [hpdecode]
          _ = decode x ^ (i.val+1) := (pow_succ (decode x) i.val).symm
      · change Prefix x (back p) (Std.Usize.wrapping_add i 1#usize).val
        rw [hsucc]
        exact write_extends_power_prefix x a i old p back hmut hpdecode hprefix
      · change (Std.Usize.wrapping_add i 1#usize).val ≤ 4
        rw [hsucc]
        omega
  have hm : ∀ s s', step x s = .ok (.cont s') → measure s' < measure s := by
    rintro ⟨a,p,i⟩ s' hbody
    have trace := step_success_trace x a p i (.cont s') hbody
    cases trace with
    | more hi old back hmut hmore p1 hmul =>
      have hip : i.val < 4 := hi
      change 4-(Std.Usize.wrapping_add i 1#usize).val < 4-i.val
      rw [successor_val i hip]
      omega
  have hlo : Aeneas.Std.loop (step x) (a,p,i) = .ok out := hrun
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property
    (step x) measure (Invariant x) (Output x) hd hc hm (a,p,i) out hinv hlo

/-- Every read of the actual successful powers4 result decodes to x^i.
The actual final iteration writes x^3 and returns without an unused x^4
multiplication. This pure function makes no oracle queries; accepted-output
refinement is sufficient for transporting its mathematical relation. -/
theorem actual_powers_four_success_decodes_powers (x : W) (out : WA) (hx : Canonical x)
    (h : AspisR1S9ProductionPairCutV1.weights.powers 4#usize x = .ok out) : Output x out := by
  have hp := AspisR1S9ActualIndexedPowersArithmeticV1.one_canonical
  have hd : decode AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ONE =
      decode x ^ (0#usize).val := by rw [one_decode]; rfl
  have hpre : Prefix x (Array.repeat 4#usize
      AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ZERO) (0#usize).val := by
    intro j value hread hj
    change j.val < 0 at hj
    omega
  exact powers_loop_success_semantics x hx _ out _ 0#usize ⟨hp,hd,hpre,by decide⟩ h

#print axioms step_success_trace
#print axioms powers_loop_success_semantics
#print axioms actual_powers_four_success_decodes_powers
end AspisR1S9ActualIndexedPowersSemanticsV1
