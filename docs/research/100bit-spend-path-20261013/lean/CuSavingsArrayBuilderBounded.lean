import CuSavingsArrayBuilder

/-! Bounded state-invariant transport for the concrete array builder.
The literal counter establishes the callback index bound at every invocation;
neither callback success nor whole-program equivalence is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsArrayBuilderBounded
open Aeneas Aeneas.Std Result CuSavingsArrayBuilder

theorem cells_naturality {T F G : Type}
    (newInst : core.ops.function.FnMut F Usize T)
    (oldInst : core.ops.function.FnMut G Usize T) (φ : F → G)
    (I : F → Prop) (bound : Nat)
    (hcall : ∀ state index, I state → index.val < bound →
      remap (fun (value,state1) => (value,φ state1)) (newInst.call_mut state index) =
        oldInst.call_mut (φ state) index)
    (hstate : ∀ state index value state1, I state → index.val < bound →
      newInst.call_mut state index = .ok (value,state1) → I state1)
    (n : Nat) (index : Usize) (state : F) (hI : I state)
    (hbound : index.val+n ≤ bound) :
    remap (fun (xs,state1) => (xs,φ state1)) (cells newInst n index state) =
      cells oldInst n index (φ state) := by
  induction n generalizing index state with
  | zero => rfl
  | succ n ih =>
    have hindex : index.val < bound := by omega
    simp only [cells]
    rw [←hcall state index hI hindex]
    cases hc : newInst.call_mut state index with
    | fail e => rfl
    | div => rfl
    | ok value =>
      rcases value with ⟨value,state1⟩
      have hI1 : I state1 := hstate state index value state1 hI hindex hc
      simp only [remap,bind_tc_ok]
      cases hi : (index + 1#usize : Result Usize) with
      | fail e => rfl
      | div => rfl
      | ok index1 =>
        have hinc := UScalar.add_equiv index 1#usize
        rw [hi] at hinc
        have hone : (1#usize).val = 1 := by scalar_tac
        have hbound1 : index1.val+n ≤ bound := by
          rw [hinc.2.1,hone]
          omega
        simp only [bind_tc_ok]
        change remap (fun (entry : {xs : List T // xs.length = n+1} × F) =>
            (entry.1,φ entry.2))
          (do let (rest,state2) ← cells newInst n index1 state1
              .ok ((⟨value::rest.val,by simp only [List.length_cons,rest.property]⟩ :
                {xs : List T // xs.length = n+1}),state2)) =
          (do let (rest,state2) ← cells oldInst n index1 (φ state1)
              .ok ((⟨value::rest.val,by simp only [List.length_cons,rest.property]⟩ :
                {xs : List T // xs.length = n+1}),state2))
        rw [←ih index1 state1 hI1 hbound1]
        cases hr : cells newInst n index1 state1 with
        | fail e => rfl
        | div => rfl
        | ok rest => rcases rest with ⟨rest,state2⟩;rfl

theorem build_naturality {T F G : Type}
    (newInst : core.ops.function.FnMut F Usize T)
    (oldInst : core.ops.function.FnMut G Usize T) (φ : F → G)
    (I : F → Prop) (N : Usize)
    (hcall : ∀ state index, I state → index.val < N.val →
      remap (fun (value,state1) => (value,φ state1)) (newInst.call_mut state index) =
        oldInst.call_mut (φ state) index)
    (hstate : ∀ state index value state1, I state → index.val < N.val →
      newInst.call_mut state index = .ok (value,state1) → I state1)
    (state : F) (hI : I state) :
    build N newInst state = build N oldInst (φ state) := by
  unfold build
  have hzero : (0#usize).val = 0 := by scalar_tac
  rw [←cells_naturality newInst oldInst φ I N.val hcall hstate N.val 0#usize state hI
    (by rw [hzero];omega)]
  cases cells newInst N.val 0#usize state <;> rfl

#print axioms cells_naturality
#print axioms build_naturality
end AspisR1.CuSavingsArrayBuilderBounded
