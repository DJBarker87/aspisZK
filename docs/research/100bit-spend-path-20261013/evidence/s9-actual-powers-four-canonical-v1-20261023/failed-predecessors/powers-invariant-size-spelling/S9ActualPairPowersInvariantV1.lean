import AspisR1S9ProductionPairCutV1.Funs
import S9ConstructorV3Loop2InnerCanonicalV1
import S9ConstructorV3InitialFactorsCanonicalV1
import S9PairArrayUpdateCanonicalV1
import S9LoopInvariantPropertyV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ActualPairPowersInvariantV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
abbrev W := AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact
abbrev WA := Array W 4#usize
abbrev State := WA × W × Usize
abbrev mapArray := @AspisR1S9CandidateFoldMapPrimitivesV1.mapArray

def Reads {A : Type} (f : W → A) (Can : A → Prop) (out : WA) : Prop :=
  ∀ (i : Usize) (v : A), Array.index_usize (mapArray f out) i = .ok v → Can v

private theorem mutable_write_preserves {A : Type} (f : W → A) (Can : A → Prop)
    (a : WA) (i : Usize) (old p : W) (back : W → WA)
    (hmut : Array.index_mut_usize a i = .ok (old, back))
    (ha : Reads f Can a) (hp : Can (f p)) : Reads f Can (back p) := by
  have hi := index_mut_bound a i old back hmut
  have hback := index_mut_back_set a i old back hi hmut
  have hlen : i.val < a.length := by simpa only [a.property] using hi
  obtain ⟨out, hupdate, hout⟩ := WP.spec_imp_exists (Array.update_spec a i p hlen)
  have hout' : out = back p := by
    calc
      out = a.set i p := hout
      _ = back p := by rw [hback]
  have hu : Array.update a i p = .ok (back p) := by simpa only [hout'] using hupdate
  exact AspisR1S9PairArrayUpdateCanonicalV1.update_preserves_canonical_reads
    f Can a i p (back p) hi hu ha hp

private def step (x : W) (s : State) : Result (ControlFlow State WA) :=
  AspisR1S9ProductionPairCutV1.weights.powers_loop.body x s.1 s.2.1 s.2.2

private def Inv {A : Type} (f : W → A) (Can : A → Prop) (s : State) : Prop :=
  Reads f Can s.1 ∧ Can (f s.2.1)

/-- This is an implementation-loop lemma: the multiplier interface is kept
explicit here and discharged by the actual Wide arithmetic producer at the
concrete entry theorem. No equality with the older FnMut powers is assumed. -/
theorem body_success_preserves {A : Type} (f : W → A) (Can : A → Prop)
    (x : W) (hx : Can (f x))
    (hmul : ∀ p p1, Can (f p) →
      AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.mul p x = .ok p1 →
      Can (f p1))
    (s : State) (flow : ControlFlow State WA) (hs : Inv f Can s)
    (hbody : step x s = .ok flow) :
    match flow with
    | .done out => Reads f Can out
    | .cont next => Inv f Can next := by
  rcases s with ⟨out, p, i⟩
  rcases hs with ⟨hout, hp⟩
  unfold step AspisR1S9ProductionPairCutV1.weights.powers_loop.body at hbody
  split at hbody
  · obtain ⟨mutPair, hmut, hbody⟩ := bind_success_inv _ _ _ hbody
    rcases mutPair with ⟨old, back⟩
    simp only [lift, bind_tc_ok] at hbody
    split at hbody
    · have he := Result.ok.inj hbody
      subst flow
      exact mutable_write_preserves f Can out i old p back hmut hout hp
    · obtain ⟨p1, hp1, hbody⟩ := bind_success_inv _ _ _ hbody
      have he := Result.ok.inj hbody
      subst flow
      exact ⟨mutable_write_preserves f Can out i old p back hmut hout hp,
        hmul p p1 hp hp1⟩
  · have he := Result.ok.inj hbody
    subst flow
    exact hout

private theorem successor_val (i : Usize) (hi : i.val < 4) :
    (Std.Usize.wrapping_add i 1#usize).val = i.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  have hone : (1#usize : Usize).val = 1 := rfl
  have hb : i.val + 1 ≤ UScalar.cMax .Usize := by
    have := Usize.cMax_bound
    scalar_tac
  have hlt := UScalar.bound_suffices .Usize (i.val + 1) hb
  rw [hone, Nat.mod_eq_of_lt hlt]

private def measure (s : State) : Nat := 4 - s.2.2.val

private theorem body_cont_decreases (x : W) (s next : State)
    (hbody : step x s = .ok (.cont next)) : measure next < measure s := by
  rcases s with ⟨out, p, i⟩
  unfold step AspisR1S9ProductionPairCutV1.weights.powers_loop.body at hbody
  split at hbody
  · rename_i hi
    obtain ⟨mutPair, hmut, hbody⟩ := bind_success_inv _ _ _ hbody
    rcases mutPair with ⟨old, back⟩
    simp only [lift, bind_tc_ok] at hbody
    split at hbody
    · cases hbody
    · obtain ⟨p1, hp1, hbody⟩ := bind_success_inv _ _ _ hbody
      have he := ControlFlow.cont.inj (Result.ok.inj hbody)
      subst next
      have hib : i.val < 4 := by exact hi
      simp only [measure]
      rw [successor_val i hib]
      omega
  · cases hbody

/-- Canonicality is preserved by the exact actual32 indexed powers loop,
including its early return before the unused final multiplication. -/
theorem powers_loop_success_reads {A : Type} (f : W → A) (Can : A → Prop)
    (x : W) (hx : Can (f x))
    (hmul : ∀ p p1, Can (f p) →
      AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.mul p x = .ok p1 →
      Can (f p1))
    (out result : WA) (p : W) (i : Usize)
    (hout : Reads f Can out) (hp : Can (f p))
    (hrun : AspisR1S9ProductionPairCutV1.weights.powers_loop x out p i = .ok result) :
    Reads f Can result := by
  have hd : ∀ s r, Inv f Can s → step x s = .ok (.done r) → Reads f Can r := by
    intro s r hs hb
    exact body_success_preserves f Can x hx hmul s (.done r) hs hb
  have hc : ∀ s s', Inv f Can s → step x s = .ok (.cont s') → Inv f Can s' := by
    intro s s' hs hb
    exact body_success_preserves f Can x hx hmul s (.cont s') hs hb
  have hloop : Aeneas.Std.loop (step x) (out, p, i) = .ok result := by
    exact hrun
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property
    (step x) measure (Inv f Can) (Reads f Can) hd hc (body_cont_decreases x)
    (out, p, i) result ⟨hout, hp⟩ hloop

/-- The source entry initializes the exact array with ZERO and running
product with ONE. The concrete arithmetic theorem supplies these three
arithmetic facts; the indexed control flow and mutable writes are proved here. -/
theorem powers_four_success_reads {A : Type} (f : W → A) (Can : A → Prop)
    (x : W) (result : WA) (hx : Can (f x))
    (hzero : Can (f AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ZERO))
    (hone : Can (f AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ONE))
    (hmul : ∀ p p1, Can (f p) →
      AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.mul p x = .ok p1 →
      Can (f p1))
    (hrun : AspisR1S9ProductionPairCutV1.weights.powers 4#usize x = .ok result) :
    Reads f Can result := by
  have hinit : Reads f Can (Array.repeat 4#usize
      AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ZERO) :=
    AspisR1S9ConstructorV3InitialFactorsCanonicalV1.repeated_mapped_reads f Can
      4#usize _ hzero
  exact powers_loop_success_reads f Can x hx hmul _ result _ 0#usize hinit hone hrun

#print axioms body_success_preserves
#print axioms powers_loop_success_reads
#print axioms powers_four_success_reads
end AspisR1S9ActualPairPowersInvariantV1
