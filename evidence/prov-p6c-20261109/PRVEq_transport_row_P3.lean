-- PCVE_ P3e: domain equality for the transport row family. Fresh (overflow-OFF) text copied from PCQH_L025 source (fresh source sha256 693741a9...).
import Aeneas
import RPz7_FIo_NativeFuns
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace FIo_Native
namespace PRVFresh_RPz7_FIo_NativeFuns_h2
/- PCQH encoding bridge (recorded in PCQH_HAND_MODELS.json / PCQH_CLASSIFICATIONS.json PCQH-C2): with overflow checks OFF the extended Aeneas
   (b59d5188) translates the Rust shift operator `x >> n` on `usize` as `Std.Usize.wrapping_shr x n`, passing the right operand at ITS OWN Rust type
   (`9#i32`, or a `Usize`), whereas the library signature is `Usize.wrapping_shr : Usize -> U32 -> Usize`, so the emitted text does not elaborate.
   The bridge below gives the emitted call the Rust meaning: the shift amount is converted by `as u32` (the library's `wrapping_shr` then masks it
   modulo the bit width, which is the unchecked-`>>` behaviour of Rust with overflow checks off). Name resolution inside the fresh namespace prefers this
   definition; it delegates to the library function. -/
class ShrAmt (α : Type) where
  toU32 : α → Std.U32
instance : ShrAmt Std.I32 := ⟨fun y => IScalar.hcast .U32 y⟩
instance : ShrAmt Std.Usize := ⟨fun y => UScalar.cast .U32 y⟩
def Std.Usize.wrapping_shr {α : Type} [ShrAmt α] (x : Std.Usize) (y : α) : Std.Usize :=
  _root_.Aeneas.Std.Usize.wrapping_shr x (ShrAmt.toU32 y)
def Std.Usize.wrapping_shl {α : Type} [ShrAmt α] (x : Std.Usize) (y : α) : Std.Usize :=
  _root_.Aeneas.Std.Usize.wrapping_shl x (ShrAmt.toU32 y)



/-- [aspis_r1_cost_probe::transport::{impl core::cmp::PartialEq<aspis_r1_cost_probe::transport::Variant> for aspis_r1_cost_probe::transport::Variant}::eq]:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 2:26-2:35
    Visibility: public -/
def transport.Variant.Insts.CoreCmpPartialEqVariant.eq
  (self : transport.Variant) (other : transport.Variant) : Result Bool := do
  let self1 := read_discriminant self
  let other1 := read_discriminant other
  ok (self1 = other1)

/-- [aspis_r1_cost_probe::transport::TAU]
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 4:0-4:44
    Visibility: public -/
@[global_simps, irreducible]
def transport.TAU : Array Std.Usize 5#usize :=
  Array.make 5#usize [ 3#usize, 4#usize, 2#usize, 0#usize, 1#usize ]

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::row]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 13:8-13:62
    Visibility: public -/
def transport.Variant.row_loop.body
  (j : Std.Usize) (iter : core.ops.range.Range Std.Usize) (out : Std.Usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × Std.Usize)
    Std.Usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done out)
  | some d =>
    let i ← lift (Std.Usize.wrapping_mul 2#usize d)
    let i1 ← lift (Std.Usize.wrapping_shr j i)
    let i2 ← lift (i1 &&& 3#usize)
    let i3 ← Array.index_usize transport.TAU d
    let i4 ← lift (Std.Usize.wrapping_mul 2#usize i3)
    let i5 ← lift (Std.Usize.wrapping_shl i2 i4)
    let out1 ← lift (out ||| i5)
    ok (cont (iter1, out1))

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::row]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 13:8-13:62
    Visibility: public -/
def transport.Variant.row_loop
  (iter : core.ops.range.Range Std.Usize) (j : Std.Usize) (out : Std.Usize) :
  Result Std.Usize
  := do
  loop
    (fun (iter1, out1) => transport.Variant.row_loop.body j iter1 out1)
    (iter, out)

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::row]:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 10:4-15:5
    Visibility: public -/
def transport.Variant.row
  (self : transport.Variant) (j : Std.Usize) : Result Std.Usize := do
  let b ←
    transport.Variant.Insts.CoreCmpPartialEqVariant.eq self transport.Variant.D
  if b
  then
    let a ← aspis_core.r0.transport.COEFFICIENT_TO_ROW
    let i ← Array.index_usize a j
    ok (UScalar.cast .Usize i)
  else
    transport.Variant.row_loop { start := 0#usize, «end» := 5#usize } j
      0#usize

end PRVFresh_RPz7_FIo_NativeFuns_h2
end FIo_Native
section PCVEhelpers
open Aeneas Aeneas.Std Result ControlFlow Error
open Lean.Order

namespace PRVH

/-- checked `x >>> i` (Usize by Usize) equals the wrapping shift by `i as u32` whenever the amount is below 32 (so below `Usize.numBits`, which is 32 or 64). -/
theorem usize_shr_usize (x i : Std.Usize) (h : i.val < 32) :
    (x >>> i : Result Std.Usize) = ok (Std.Usize.wrapping_shr x (UScalar.cast .U32 i)) := by
  show UScalar.shiftRight_UScalar x i = _
  unfold UScalar.shiftRight_UScalar
  have hc : (UScalar.cast .U32 i).val = i.val := by
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by simp [UScalarTy.numBits]; omega)
  rcases System.Platform.numBits_eq with hb | hb
  · simp [UScalar.shiftRight, Std.Usize.wrapping_shr, UScalar.wrapping_shr, UScalarTy.numBits, hc, hb]
    rw [if_pos h, Nat.mod_eq_of_lt h]
  · simp [UScalar.shiftRight, Std.Usize.wrapping_shr, UScalar.wrapping_shr, UScalarTy.numBits, hc, hb]
    rw [if_pos (by omega), Nat.mod_eq_of_lt (by omega)]

/-- checked `x <<< i` (Usize by Usize) equals the wrapping shift by `i as u32` whenever the amount is below 32. -/
theorem usize_shl_usize (x i : Std.Usize) (h : i.val < 32) :
    (x <<< i : Result Std.Usize) = ok (Std.Usize.wrapping_shl x (UScalar.cast .U32 i)) := by
  show UScalar.shiftLeft_UScalar x i = _
  unfold UScalar.shiftLeft_UScalar
  have hc : (UScalar.cast .U32 i).val = i.val := by
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by simp [UScalarTy.numBits]; omega)
  rcases System.Platform.numBits_eq with hb | hb
  · simp [UScalar.shiftLeft, Std.Usize.wrapping_shl, UScalar.wrapping_shl, UScalarTy.numBits, hc, hb]
    rw [if_pos h, Nat.mod_eq_of_lt h]
  · simp [UScalar.shiftLeft, Std.Usize.wrapping_shl, UScalar.wrapping_shl, UScalarTy.numBits, hc, hb]
    rw [if_pos (by omega), Nat.mod_eq_of_lt (by omega)]

end PRVH
#print axioms PRVH.usize_shr_usize
#print axioms PRVH.usize_shl_usize

namespace PRVC

/-- one step of the Aeneas `loop` functional -/
def bs {α β : Type _} (body : α → Result (ControlFlow α β)) (h : α → Result β) (x : α) : Result β :=
  match body x with
  | ok r => match r with
    | ControlFlow.cont x' => h x'
    | ControlFlow.done y => ok y
  | fail e => fail e
  | div => div

theorem bs_mono {α β : Type _} (body : α → Result (ControlFlow α β)) (h1 h2 : α → Result β)
    (hle : ∀ x, h1 x ⊑ h2 x) (x : α) : bs body h1 x ⊑ bs body h2 x := by
  unfold bs
  cases body x with
  | ok r => cases r with
    | cont x' => exact hle x'
    | done y => exact PartialOrder.rel_refl
  | fail e => exact PartialOrder.rel_refl
  | div => exact PartialOrder.rel_refl

theorem loop_unfold {α β : Type _} (body : α → Result (ControlFlow α β)) (x : α) :
    loop body x = bs body (loop body) x := by
  rw [loop]; rfl
#print axioms loop_unfold


theorem adm_le {β : Type _} (g : Result β) : admissible (fun r : Result β => r ⊑ g) :=
  admissible_flatOrder (b := (div : Result β)) (fun r : Result β => r ⊑ g) FlatOrder.rel.bot

theorem loop_le {α β : Type _} (body : α → Result (ControlFlow α β)) (g : α → Result β)
    (hg : ∀ x, bs body g x ⊑ g x) : ∀ x, loop body x ⊑ g x := by
  refine loop.fixpoint_induct body (fun f => ∀ x, f x ⊑ g x) ?_ ?_
  · exact admissible_pi_apply (fun x (r : Result β) => r ⊑ g x) (fun x => adm_le (g x))
  · intro f hf x
    exact PartialOrder.rel_trans (bs_mono body f g hf x) (hg x)

theorem loop_eq {α β : Type _} (body : α → Result (ControlFlow α β)) (g : α → Result β)
    (hfix : ∀ x, g x = bs body g x)
    (hmin : ∀ h : α → Result β, (∀ x, bs body h x ⊑ h x) → ∀ x, g x ⊑ h x) :
    ∀ x, loop body x = g x := by
  intro x
  have h1 : loop body x ⊑ g x := loop_le body g (fun y => by rw [← hfix y]) x
  have h2 : g x ⊑ loop body x :=
    hmin (loop body) (fun y => by rw [← loop_unfold]) x
  exact PartialOrder.rel_antisymm h1 h2
#print axioms loop_eq


/-- curried-pair admissibility helpers for `X.fixpoint_induct` motives -/
theorem adm_le1 {α β : Type _} (h : α → Result β) :
    admissible (fun f : α → Result β => ∀ a, f a ⊑ h a) :=
  admissible_pi_apply (fun a (r : Result β) => r ⊑ h a) (fun a => adm_le (h a))

theorem adm_le2 {α₁ α₂ β : Type _} (h : α₁ → α₂ → Result β) :
    admissible (fun f : α₁ → α₂ → Result β => ∀ a b, f a b ⊑ h a b) :=
  admissible_pi_apply (fun a (g : α₂ → Result β) => ∀ b, g b ⊑ h a b)
    (fun a => adm_le1 (h a))

theorem adm_le3 {α₁ α₂ α₃ β : Type _} (h : α₁ → α₂ → α₃ → Result β) :
    admissible (fun f : α₁ → α₂ → α₃ → Result β => ∀ a b c, f a b c ⊑ h a b c) :=
  admissible_pi_apply (fun a (g : α₂ → α₃ → Result β) => ∀ b c, g b c ⊑ h a b c)
    (fun a => adm_le2 (h a))

theorem adm_le4 {α₁ α₂ α₃ α₄ β : Type _} (h : α₁ → α₂ → α₃ → α₄ → Result β) :
    admissible (fun f : α₁ → α₂ → α₃ → α₄ → Result β => ∀ a b c d, f a b c d ⊑ h a b c d) :=
  admissible_pi_apply (fun a (g : α₂ → α₃ → α₄ → Result β) => ∀ b c d, g b c d ⊑ h a b c d)
    (fun a => adm_le3 (h a))


theorem bs_bind {α β : Type _} (body : α → Result (ControlFlow α β)) (h : α → Result β) (x : α) :
    bs body h x = Bind.bind (body x) (fun r => match r with
      | ControlFlow.cont x' => h x'
      | ControlFlow.done y => ok y) := by
  unfold bs
  cases body x with
  | ok r => cases r <;> rfl
  | fail e => rfl
  | div => rfl

theorem ite_bind {α β : Type _} (c : Prop) [Decidable c] (a b : Result α) (K : α → Result β) :
    Bind.bind (if c then a else b) K = if c then Bind.bind a K else Bind.bind b K := by
  by_cases hc : c <;> simp [hc]

theorem dite_bind {α β : Type _} (c : Prop) [Decidable c] (a : c → Result α) (b : ¬c → Result α)
    (K : α → Result β) :
    Bind.bind (dite c a b) K = dite c (fun h => Bind.bind (a h) K) (fun h => Bind.bind (b h) K) := by
  by_cases hc : c <;> simp [hc]


theorem bind_congr {α β : Type _} {m : Result α} {f f' : α → Result β} (h : ∀ a, f a = f' a) :
    Bind.bind m f = Bind.bind m f' := by
  have : f = f' := funext h
  rw [this]

theorem ite_congr' {α : Type _} (c : Prop) [Decidable c] {a a' b b' : Result α}
    (h1 : a = a') (h2 : b = b') : (if c then a else b) = (if c then a' else b') := by
  rw [h1, h2]

theorem dite_congr' {α : Type _} (c : Prop) [Decidable c] {a a' : c → Result α} {b b' : ¬c → Result α}
    (h1 : ∀ h, a h = a' h) (h2 : ∀ h, b h = b' h) : dite c a b = dite c a' b' := by
  have e1 : a = a' := funext h1
  have e2 : b = b' := funext h2
  rw [e1, e2]


theorem rel_of_eq' {γ : Type _} [Lean.Order.PartialOrder γ] {a b : γ} (h : a = b) : a ⊑ b := by
  rw [h]

theorem loop_eq_of_le {α β : Type _} (body : α → Result (ControlFlow α β)) (g : α → Result β)
    (hpre : ∀ x, bs body g x ⊑ g x) (hge : ∀ x, g x ⊑ loop body x) :
    ∀ x, loop body x = g x :=
  fun x => PartialOrder.rel_antisymm (loop_le body g hpre x) (hge x)
#print axioms loop_eq_of_le

theorem adm_le5 {α1 α2 α3 α4 α5 β : Type _} (h : α1 → α2 → α3 → α4 → α5 → Result β) :
    admissible (fun f : α1 → α2 → α3 → α4 → α5 → Result β => ∀ x1 x2 x3 x4 x5, f x1 x2 x3 x4 x5 ⊑ h x1 x2 x3 x4 x5) :=
  admissible_pi_apply (fun x1 (g : α2 → α3 → α4 → α5 → Result β) => ∀ x2 x3 x4 x5, g x2 x3 x4 x5 ⊑ h x1 x2 x3 x4 x5)
    (fun a => adm_le4 (h a))

theorem adm_le6 {α1 α2 α3 α4 α5 α6 β : Type _} (h : α1 → α2 → α3 → α4 → α5 → α6 → Result β) :
    admissible (fun f : α1 → α2 → α3 → α4 → α5 → α6 → Result β => ∀ x1 x2 x3 x4 x5 x6, f x1 x2 x3 x4 x5 x6 ⊑ h x1 x2 x3 x4 x5 x6) :=
  admissible_pi_apply (fun x1 (g : α2 → α3 → α4 → α5 → α6 → Result β) => ∀ x2 x3 x4 x5 x6, g x2 x3 x4 x5 x6 ⊑ h x1 x2 x3 x4 x5 x6)
    (fun a => adm_le5 (h a))

theorem uncurry_proj {α β γ : Type _} (f : α → β → γ) (p : α × β) :
    Aeneas.Std.uncurry f p = f p.1 p.2 := by cases p; rfl

/-- normalise both sides, one side at a time (a whole-goal `simp` can refuse on dependent numerals) -/
macro "prv_norm" : tactic => `(tactic| (
  try (conv_lhs => simp only [bind_assoc_eq, ite_bind, dite_bind, bind_tc_ok, Aeneas.Std.bind_ok, Aeneas.Std.uncurry_apply_pair, uncurry_proj])
  try (conv_rhs => simp only [bind_assoc_eq, ite_bind, dite_bind, bind_tc_ok, Aeneas.Std.bind_ok, Aeneas.Std.uncurry_apply_pair, uncurry_proj])))

/-- push the loop continuation inward and match the two do-block shapes -/
macro "prv_peel" : tactic => `(tactic| (
  prv_norm
  repeat (first
    | with_reducible rfl
    | (apply PRVC.bind_congr; intro a; try (obtain ⟨_, _⟩ := a); prv_norm)
    | (apply PRVC.ite_congr'; prv_norm)
    | (apply PRVC.dite_congr' <;> intro h)
    | (split <;> prv_norm))))

end PRVC


namespace PRVH

/-- A domain-restricted loop comparison: if two loop bodies agree on an invariant domain that the first body preserves, the loops agree on that domain. -/
theorem loop_le_dom {α β : Type _} (F G : α → Result (ControlFlow α β)) (Inv : α → Prop)
    (hFG : ∀ x, Inv x → F x = G x)
    (hpres : ∀ x x', Inv x → F x = ok (ControlFlow.cont x') → Inv x') :
    ∀ x, Inv x → loop F x ⊑ loop G x := by
  have adm : admissible (fun f : α → Result β => ∀ x, Inv x → f x ⊑ loop G x) := by
    apply admissible_pi_apply (fun x (r : Result β) => Inv x → r ⊑ loop G x)
    intro x
    by_cases h : Inv x
    · simpa [h] using PRVC.adm_le (loop G x)
    · simp [h]
      exact fun c _ _ => trivial
  refine loop.fixpoint_induct F (fun f => ∀ x, Inv x → f x ⊑ loop G x) adm ?_
  intro f hf x hx
  rw [PRVC.loop_unfold G x]
  unfold PRVC.bs
  rw [← hFG x hx]
  dsimp only
  cases hFx : F x with
  | ok r =>
    cases r with
    | cont x' => exact hf x' (hpres x x' hx hFx)
    | done y => exact PartialOrder.rel_refl
  | fail e => exact PartialOrder.rel_refl
  | div => exact PartialOrder.rel_refl

theorem loop_eq_dom {α β : Type _} (F G : α → Result (ControlFlow α β)) (Inv : α → Prop)
    (hFG : ∀ x, Inv x → F x = G x)
    (hpres : ∀ x x', Inv x → F x = ok (ControlFlow.cont x') → Inv x') :
    ∀ x, Inv x → loop F x = loop G x := by
  intro x hx
  apply PartialOrder.rel_antisymm
  · exact loop_le_dom F G Inv hFG hpres x hx
  · refine loop_le_dom G F Inv (fun y hy => (hFG y hy).symm) ?_ x hx
    intro y y' hy hG
    exact hpres y y' hy (by rw [hFG y hy]; exact hG)

/-- `Range::next` keeps the end of the range. -/
theorem range_next_end {A : Type} (S : core.iter.range.Step A) (r r1 : core.ops.range.Range A)
    (o : Option A) (h : core.iter.range.IteratorRange.next S r = ok (o, r1)) :
    r1.«end» = r.«end» := by
  unfold core.iter.range.IteratorRange.next at h
  cases hlt : S.partialOrdInst.lt r.start r.«end» with
  | fail e => simp [hlt] at h
  | div => simp [hlt] at h
  | ok c =>
    cases c with
    | false => simp [hlt] at h; rw [← h.2]
    | true =>
      cases hcl : S.cloneInst.clone r.start with
      | fail e => simp [hlt, hcl] at h
      | div => simp [hlt, hcl] at h
      | ok r' =>
        cases hfc : S.forward_checked r' 1#usize with
        | fail e => simp [hlt, hcl, hfc] at h
        | div => simp [hlt, hcl, hfc] at h
        | ok n =>
          cases n with
          | none => simp [hlt, hcl, hfc] at h
          | some n => simp [hlt, hcl, hfc] at h; rw [← h.2]

end PRVH
#print axioms PRVH.loop_le_dom
#print axioms PRVH.loop_eq_dom
#print axioms PRVH.range_next_end
end PCVEhelpers
set_option maxHeartbeats 200000 in
theorem PRVEq.RPz7_FIo_NativeFuns_h2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq : @FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq = @FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq := by
  first | (trace "PRV-S1 PRVEq.RPz7_FIo_NativeFuns_h2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq"; rfl) | (trace "PRV-S2 PRVEq.RPz7_FIo_NativeFuns_h2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq"; delta FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq; try rfl; done)
#print axioms PRVEq.RPz7_FIo_NativeFuns_h2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq

set_option maxHeartbeats 200000 in
theorem PRVEq.RPz7_FIo_NativeFuns_h2.transport.TAU : @FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.TAU = @FIo_Native.transport.TAU := by
  first | (trace "PRV-S1 PRVEq.RPz7_FIo_NativeFuns_h2.transport.TAU"; rfl) | (trace "PRV-S2 PRVEq.RPz7_FIo_NativeFuns_h2.transport.TAU"; delta FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.TAU FIo_Native.transport.TAU; try rfl; done)
#print axioms PRVEq.RPz7_FIo_NativeFuns_h2.transport.TAU

/-- PCQH helper: successful `Range<usize>::next` returning `some d` has `d < end`. -/
theorem PRVEq.RPz7_FIo_NativeFuns_h2.range_next_usize_lt (r r1 : core.ops.range.Range Std.Usize) (d : Std.Usize)
    (h : core.iter.range.IteratorRange.next core.iter.range.StepUsize r = ok (some d, r1)) :
    d.val < r.«end».val := by
  unfold core.iter.range.IteratorRange.next at h
  simp [core.iter.range.StepUsize, core.iter.range.UScalarStep, core.cmp.PartialOrdUsize, core.clone.CloneUsize,
    liftFun2, liftFun1, core.cmp.impls.PartialOrdUsize.lt, core.clone.impls.CloneUsize.clone] at h
  by_cases hlt : r.start.val < r.«end».val
  · rw [if_pos hlt] at h
    cases hf : core.iter.range.UScalarStep.forward_checked r.start 1#usize with
    | fail e => simp [hf] at h
    | div => simp [hf] at h
    | ok n =>
      cases n with
      | none => simp [hf] at h
      | some n =>
        simp [hf] at h
        rw [← h.1]
        exact hlt
  · rw [if_neg hlt] at h
    simp at h

/-- PCQH helper: every element of the gate `TAU` is at most 4. -/
theorem PRVEq.RPz7_FIo_NativeFuns_h2.TAU_le (d i3 : Std.Usize) (h : FIo_Native.transport.TAU.index_usize d = ok i3) : i3.val ≤ 4 := by
  unfold Std.Array.index_usize at h
  cases hq : (FIo_Native.transport.TAU)[d]? with
  | none => simp [hq] at h
  | some x =>
    simp [hq] at h
    rw [← h]
    rw [Std.Array.getElem?_Usize_eq] at hq
    have hmem : x ∈ ([3#usize, 4#usize, 2#usize, 0#usize, 1#usize] : List Std.Usize) := by
      have h2 : x ∈ (FIo_Native.transport.TAU : Std.Array Std.Usize 5#usize).val := List.mem_of_getElem? hq
      unfold FIo_Native.transport.TAU at h2
      exact h2
    simp at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl <;> scalar_tac

theorem PRVEq.RPz7_FIo_NativeFuns_h2.wmul2_lt (x : Std.Usize) (hx : x.val < 16) : (Std.Usize.wrapping_mul 2#usize x).val < 32 := by
  rw [Std.Usize.wrapping_mul_val_eq]
  have h2 : (2#usize).val = 2 := by scalar_tac
  have hs : 32 < UScalar.size UScalarTy.Usize := by
    rw [UScalar.size_UScalarTyUsize, Std.Usize.size_def]
    rcases System.Platform.numBits_eq with h | h <;> simp [Std.Usize.numBits, h]
  rw [h2, Nat.mod_eq_of_lt (by omega)]
  omega

theorem PRVEq.RPz7_FIo_NativeFuns_h2.fresh_shr_eq (j i : Std.Usize) : FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.Std.Usize.wrapping_shr j i = Aeneas.Std.Usize.wrapping_shr j (UScalar.cast .U32 i) := rfl
theorem PRVEq.RPz7_FIo_NativeFuns_h2.fresh_shl_eq (j i : Std.Usize) : FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.Std.Usize.wrapping_shl j i = Aeneas.Std.Usize.wrapping_shl j (UScalar.cast .U32 i) := rfl

theorem PRVEq.RPz7_FIo_NativeFuns_h2.bind_congr_ok {α β : Type} (m : Result α) (f g : α → Result β) (h : ∀ a, m = ok a → f a = g a) :
    Bind.bind m f = Bind.bind m g := by
  cases hm : m with
  | ok a => simp only [bind_tc_ok]; exact h a hm
  | fail e => rfl
  | div => rfl

/-- PCQH: the fresh body preserves the end of the range. -/
theorem PRVEq.RPz7_FIo_NativeFuns_h2.body_end (j : Std.Usize) (iter : core.ops.range.Range Std.Usize) (out : Std.Usize) (iter2 : core.ops.range.Range Std.Usize) (out2 : Std.Usize)
    (h : FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body j iter out = ok (ControlFlow.cont (iter2, out2))) : iter2.«end» = iter.«end» := by
  unfold FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body at h
  cases hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e => simp [hn] at h
  | div => simp [hn] at h
  | ok p =>
    obtain ⟨o, iter1⟩ := p
    have he := PRVH.range_next_end core.iter.range.StepUsize iter iter1 o hn
    simp only [hn, bind_tc_ok] at h
    cases o with
    | none => simp at h
    | some d =>
      simp only [lift, bind_tc_ok] at h
      cases h3 : FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.TAU.index_usize d with
      | fail e => simp [h3] at h
      | div => simp [h3] at h
      | ok i3 =>
        simp [h3] at h
        rw [← h.1]
        exact he


/-- PCVE step reductions: the matcher inside `row_loop.body` is not reduced by `cases o` (the goal keeps
`let (o, iter1) := (some d, iter1); match_1 ...` with the bound `d` inside a lambda, which is why `e_shr` about the free `d`
never matched in PCQH_L022..L025). These two lemmas reduce each side to its explicit `some d` continuation by `rfl`. -/
theorem PCVE.fresh_body_some (j : Std.Usize) (iter iter1 : core.ops.range.Range Std.Usize) (out d : Std.Usize)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (some d, iter1)) :
    FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body j iter out =
      (do
        let i ← lift (Std.Usize.wrapping_mul 2#usize d)
        let i1 ← lift (FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.Std.Usize.wrapping_shr j i)
        let i2 ← lift (i1 &&& 3#usize)
        let i3 ← Array.index_usize FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.TAU d
        let i4 ← lift (Std.Usize.wrapping_mul 2#usize i3)
        let i5 ← lift (FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.Std.Usize.wrapping_shl i2 i4)
        let out1 ← lift (out ||| i5)
        ok (ControlFlow.cont (iter1, out1))) := by
  unfold FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body
  rw [hn]
  rfl

theorem PCVE.gate_body_some (j : Std.Usize) (iter iter1 : core.ops.range.Range Std.Usize) (out d : Std.Usize)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (some d, iter1)) :
    FIo_Native.transport.Variant.row_loop.body j iter out =
      (do
        let i ← lift (Std.Usize.wrapping_mul 2#usize d)
        let i1 ← (j >>> i)
        let i2 ← lift (i1 &&& 3#usize)
        let i3 ← Array.index_usize FIo_Native.transport.TAU d
        let i4 ← lift (Std.Usize.wrapping_mul 2#usize i3)
        let i5 ← (i2 <<< i4)
        let out1 ← lift (out ||| i5)
        ok (ControlFlow.cont (iter1, out1))) := by
  unfold FIo_Native.transport.Variant.row_loop.body
  rw [hn]
  rfl
#print axioms PCVE.fresh_body_some
#print axioms PCVE.gate_body_some

theorem PCVE.transport.Variant.row_loop.body_dom (j : Std.Usize) (iter : core.ops.range.Range Std.Usize) (out : Std.Usize)
    (hend : iter.«end».val ≤ 16) :
    FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body j iter out = FIo_Native.transport.Variant.row_loop.body j iter out := by
  cases hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e =>
    unfold FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body FIo_Native.transport.Variant.row_loop.body
    rw [hn]; rfl
  | div =>
    unfold FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body FIo_Native.transport.Variant.row_loop.body
    rw [hn]; rfl
  | ok p =>
    obtain ⟨o, iter1⟩ := p
    cases o with
    | none =>
      unfold FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body FIo_Native.transport.Variant.row_loop.body
      rw [hn]; rfl
    | some d =>
      rw [PCVE.fresh_body_some j iter iter1 out d hn, PCVE.gate_body_some j iter iter1 out d hn]
      have hd : d.val < 16 := by have := PRVEq.RPz7_FIo_NativeFuns_h2.range_next_usize_lt iter iter1 d hn; omega
      have hi := PRVEq.RPz7_FIo_NativeFuns_h2.wmul2_lt d hd
      have e_shr : (j >>> Std.Usize.wrapping_mul 2#usize d : Result Std.Usize)
          = ok (Aeneas.Std.Usize.wrapping_shr j (UScalar.cast .U32 (Std.Usize.wrapping_mul 2#usize d))) :=
        PRVH.usize_shr_usize j _ hi
      simp only [lift, bind_tc_ok, e_shr, PRVEq.RPz7_FIo_NativeFuns_h2.transport.TAU,
        PRVEq.RPz7_FIo_NativeFuns_h2.fresh_shr_eq, PRVEq.RPz7_FIo_NativeFuns_h2.fresh_shl_eq]
      cases h3 : Array.index_usize FIo_Native.transport.TAU d with
      | fail e => simp [h3]
      | div => simp [h3]
      | ok i3 =>
        have h4 := PRVEq.RPz7_FIo_NativeFuns_h2.wmul2_lt i3 (by have := PRVEq.RPz7_FIo_NativeFuns_h2.TAU_le d i3 h3; omega)
        have e_shl := PRVH.usize_shl_usize ((Aeneas.Std.Usize.wrapping_shr j (UScalar.cast .U32 (Std.Usize.wrapping_mul 2#usize d))) &&& 3#usize)
          (Std.Usize.wrapping_mul 2#usize i3) h4
        simp only [h3, bind_tc_ok, e_shl]
#print axioms PCVE.transport.Variant.row_loop.body_dom

theorem PCVE.transport.Variant.row_loop_dom (iter : core.ops.range.Range Std.Usize) (j out : Std.Usize)
    (hend : iter.«end».val ≤ 16) :
    FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop iter j out = FIo_Native.transport.Variant.row_loop iter j out := by
  unfold FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop FIo_Native.transport.Variant.row_loop
  refine PRVH.loop_eq_dom _ _ (fun x => x.1.«end».val ≤ 16) ?_ ?_ (iter, out) hend
  · rintro ⟨iter1, out1⟩ h
    exact PCVE.transport.Variant.row_loop.body_dom j iter1 out1 h
  · rintro ⟨iter1, out1⟩ ⟨iter2, out2⟩ h hF
    have := PRVEq.RPz7_FIo_NativeFuns_h2.body_end j iter1 out1 iter2 out2 hF
    simp only at h ⊢
    rw [this]
    exact h
#print axioms PCVE.transport.Variant.row_loop_dom

/-- No domain hypothesis: `row` fixes the range to `0..5` (end 5 <= 16). -/
theorem PCVE.transport.Variant.row : @FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row = @FIo_Native.transport.Variant.row := by
  have hr : ∀ j : Std.Usize, FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop { start := 0#usize, «end» := 5#usize } j 0#usize
      = FIo_Native.transport.Variant.row_loop { start := 0#usize, «end» := 5#usize } j 0#usize :=
    fun j => PCVE.transport.Variant.row_loop_dom _ j 0#usize (by scalar_tac)
  delta FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row FIo_Native.transport.Variant.row
  simp only [PRVEq.RPz7_FIo_NativeFuns_h2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq, hr]
#print axioms PCVE.transport.Variant.row
