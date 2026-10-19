import Aeneas

/-! A concrete ordered, state-threading interpretation of array::from_fn.
It handles arbitrary callback failures/divergence; no callback-success or
optimization-equivalence axiom is introduced. Standard-library source
admission remains separate from this interpretation's checked properties. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AspisR1.CuSavingsArrayBuilder
open Aeneas Aeneas.Std Result

def remap {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

def cells {T F : Type} (inst : core.ops.function.FnMut F Usize T) :
    (n : Nat) → Usize → F → Result ({xs : List T // xs.length = n} × F)
  | 0, _, state => .ok (⟨[],rfl⟩,state)
  | n+1, index, state => do
    let (value,state1) ← inst.call_mut state index
    let index1 ← index + 1#usize
    let (rest,state2) ← cells inst n index1 state1
    .ok (⟨value::rest.val,by simp only [List.length_cons,rest.property]⟩,state2)

def build {T F : Type} (N : Usize) (inst : core.ops.function.FnMut F Usize T)
    (state : F) : Result (Array T N) := do
  let (xs,_) ← cells inst N.val 0#usize state
  .ok ⟨xs.val,xs.property⟩

theorem cells_naturality {T F G : Type}
    (newInst : core.ops.function.FnMut F Usize T)
    (oldInst : core.ops.function.FnMut G Usize T) (φ : F → G)
    (hcall : ∀ state index,
      remap (fun (value,state1) => (value,φ state1)) (newInst.call_mut state index) =
        oldInst.call_mut (φ state) index)
    (n : Nat) (index : Usize) (state : F) :
    remap (fun (xs,state1) => (xs,φ state1)) (cells newInst n index state) =
      cells oldInst n index (φ state) := by
  induction n generalizing index state with
  | zero => rfl
  | succ n ih =>
    simp only [cells]
    rw [←hcall state index]
    cases hc : newInst.call_mut state index with
    | fail e => rfl
    | div => rfl
    | ok value =>
      rcases value with ⟨value,state1⟩
      simp only [remap,bind_tc_ok]
      cases hi : (index + 1#usize : Result Usize) with
      | fail e => rfl
      | div => rfl
      | ok index1 =>
        simp only [bind_tc_ok]
        rw [←ih index1 state1]
        cases hr : cells newInst n index1 state1 with
        | fail e => rfl
        | div => rfl
        | ok rest => rcases rest with ⟨rest,state2⟩;rfl

theorem build_naturality {T F G : Type}
    (newInst : core.ops.function.FnMut F Usize T)
    (oldInst : core.ops.function.FnMut G Usize T) (φ : F → G)
    (hcall : ∀ state index,
      remap (fun (value,state1) => (value,φ state1)) (newInst.call_mut state index) =
        oldInst.call_mut (φ state) index)
    (N : Usize) (state : F) :
    build N newInst state = build N oldInst (φ state) := by
  unfold build
  rw [←cells_naturality newInst oldInst φ hcall N.val 0#usize state]
  cases cells newInst N.val 0#usize state <;> rfl

#print axioms cells
#print axioms build
#print axioms cells_naturality
#print axioms build_naturality
end AspisR1.CuSavingsArrayBuilder
