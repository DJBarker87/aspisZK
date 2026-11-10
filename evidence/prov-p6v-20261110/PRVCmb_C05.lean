-- PCXB combined-import bundle PRVCmb_C05: exact file texts (import lines hoisted), with declared names renamed by PCXB_rename.py tag C05_Fjj (rule PCXB-C2): PRVC_LoopBridge.lean, PRVEq_FIn_WeightsFuns_h1.lean, PRVEq_NFN_ExtractedGeometry_h1.lean, PRVEq_NFN_ExtractedGeometry_h2.lean, PRVEq_NJA_CountBody_h1.lean, PRVEq_RPz7_FIo_NativeFuns_h1.lean, PRVH_LoopDom.lean, PRVH_Shift.lean, PRVEq_NativeFunsQ415.lean, PRVEq_AspisC2HostEmbedding_Funs.lean, PRVEq_AspisR1CircleFallback_Types.lean, PRVEq_AspisR1CircleSampleWrapper_Types.lean, PRVEq_AspisR1CurrentWide_Funs.lean, PRVEq_AspisR1Post25Sampler_Funs.lean, PRVEq_AspisR1PrefixAggregateParser_Funs.lean, PRVEq_AspisR1PublicPreparation_Types.lean, PRVEq_AspisR1Qm31SamplerIndex_Funs.lean, PRVEq_AspisR1SemanticCallExtraction_Funs.lean, PRVEq_AspisR1TerminalDecoder_Funs.lean
import Aeneas
import FIn_WeightsFuns
import PRVH_WrapAdd
import NFN_ExtractedGeometry
import NJA_CountBody
import RPz7_FIo_NativeFuns
import AspisC2HostEmbedding.Funs
import AspisR1CircleFallback.Types
import AspisR1CircleSampleWrapper.Types
import AspisR1CurrentWide.Funs
import AspisR1Post25Sampler.Funs
import AspisR1PrefixAggregateParser.Funs
import AspisR1PublicPreparation.Types
import AspisR1Qm31SamplerIndex.Funs
import AspisR1SemanticCallExtraction.Funs
import AspisR1TerminalDecoder.Funs
section PRVBundle_0
open Aeneas Aeneas.Std Result ControlFlow Error
open Lean.Order

namespace PRVC_C05_F00

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
    | (apply PRVC_C05_F00.bind_congr; intro a; try (obtain ⟨_, _⟩ := a); prv_norm)
    | (apply PRVC_C05_F00.ite_congr'; prv_norm)
    | (apply PRVC_C05_F00.dite_congr' <;> intro h)
    | (split <;> prv_norm))))

end PRVC_C05_F00

end PRVBundle_0
section PRVBundle_1
-- GENERATED by PCQH_gen_equalities.py for gate module FIn_WeightsFuns. Statements are against the gate constants of FIn_WeightsFuns.
-- fresh emission: PCQH_hf1 -> PRVFresh_C05_F01_FIn_WeightsFuns_h1; fresh source sha256 b6ef356f4f98f0af59651228ae870b3e226aae3d2ab95747c1db6d031a2af8bd
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace FIn_WeightsExtract
namespace PRVFresh_C05_F01_FIn_WeightsFuns_h1

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 31:0-44:1 -/
def field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 field.P)
  let i1 ← lift (x &&& i)
  let i2 ← lift (Std.U64.wrapping_shr x 31#u32)
  let x1 ← lift (Std.U64.wrapping_add i1 i2)
  let i3 ← lift (UScalar.cast .U64 field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← lift (Std.U64.wrapping_shr x1 31#u32)
  let x2 ← lift (Std.U64.wrapping_add i4 i5)
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= field.P
  then ok (Std.U32.wrapping_sub x3 field.P)
  else ok x3

/-- [aspis_core::field::{aspis_core::field::M31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 62:4-88:5
    Visibility: public -/
def field.M31.add (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let s ← lift (Std.U32.wrapping_add self rhs)
  if s >= field.P
  then let s1 ← lift (Std.U32.wrapping_sub s field.P)
       ok s1
  else ok s

/-- [aspis_core::field::{aspis_core::field::M31}::sub]:
    Source: 'crates/aspis-core/src/field.rs', lines 94:4-119:5
    Visibility: public -/
def field.M31.sub (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← lift (Std.U32.wrapping_add self field.P)
  let s ← lift (Std.U32.wrapping_sub i rhs)
  if s >= field.P
  then let s1 ← lift (Std.U32.wrapping_sub s field.P)
       ok s1
  else ok s

/-- [aspis_core::field::{aspis_core::field::M31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 133:4-137:5
    Visibility: public -/
def field.M31.mul (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← lift (Std.U64.wrapping_mul i i1)
  let i3 ← field.reduce_u64 i2
  ok i3

/-- [aspis_core::field::{aspis_core::field::M31}::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 153:4-155:5
    Visibility: public -/
def field.M31.reduce_u64 (value : Std.U64) : Result field.M31 := do
  let i ← field.reduce_u64 value
  ok i

/-- [aspis_core::field::{aspis_core::field::M31}::double]:
    Source: 'crates/aspis-core/src/field.rs', lines 183:4-185:5
    Visibility: public -/
def field.M31.double (self : field.M31) : Result field.M31 := do
  field.M31.add self self

/-- [aspis_core::field::{aspis_core::field::CM31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 281:4-286:5
    Visibility: public -/
def field.CM31.add
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m ← field.M31.add self.a rhs.a
  let m1 ← field.M31.add self.b rhs.b
  ok { a := m, b := m1 }

/-- [aspis_core::field::{aspis_core::field::CM31}::sub]:
    Source: 'crates/aspis-core/src/field.rs', lines 289:4-294:5
    Visibility: public -/
def field.CM31.sub
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m ← field.M31.sub self.a rhs.a
  let m1 ← field.M31.sub self.b rhs.b
  ok { a := m, b := m1 }

/-- [aspis_core::field::{aspis_core::field::CM31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 306:4-320:5
    Visibility: public -/
def field.CM31.mul
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m0 ← field.M31.mul self.a rhs.a
  let m1 ← field.M31.mul self.b rhs.b
  let i := self.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← lift (Std.U64.wrapping_add i1 i3)
  let i5 := rhs.a
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.b
  let i8 ← lift (core.convert.num.FromU64U32.from i7)
  let i9 ← lift (Std.U64.wrapping_add i6 i8)
  let i10 ← lift (Std.U64.wrapping_mul i4 i9)
  let m2 ← field.M31.reduce_u64 i10
  let m ← field.M31.sub m0 m1
  let m3 ← field.M31.sub m2 m0
  let m4 ← field.M31.sub m3 m1
  ok { a := m, b := m4 }

/-- [aspis_core::field::mul_by_r]:
    Source: 'crates/aspis-core/src/field.rs', lines 860:0-866:1 -/
def field.mul_by_r (x : field.CM31) : Result field.CM31 := do
  let m ← field.M31.double x.a
  let m1 ← field.M31.sub m x.b
  let m2 ← field.M31.double x.b
  let m3 ← field.M31.add x.a m2
  ok { a := m1, b := m3 }

end PRVFresh_C05_F01_FIn_WeightsFuns_h1
end FIn_WeightsExtract

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F01.FIn_WeightsFuns_h1.field.P : @FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.P = @FIn_WeightsExtract.field.P := by
  first | (trace "PRV-S1 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.P"; rfl) | (trace "PRV-S2 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.P"; delta FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.P FIn_WeightsExtract.field.P; try rfl; done)
#print axioms PRVEq.C05_F01.FIn_WeightsFuns_h1.field.P

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F01.FIn_WeightsFuns_h1.field.reduce_u64 : @FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.reduce_u64 = @FIn_WeightsExtract.field.reduce_u64 := by
  first | (trace "PRV-S1 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.reduce_u64"; rfl) | (trace "PRV-S2 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.reduce_u64"; delta FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.reduce_u64 FIn_WeightsExtract.field.reduce_u64; try simp only [PRVEq.C05_F01.FIn_WeightsFuns_h1.field.P]; try rfl; done)
#print axioms PRVEq.C05_F01.FIn_WeightsFuns_h1.field.reduce_u64

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.add : @FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.M31.add = @FIn_WeightsExtract.field.M31.add := by
  first | (trace "PRV-S1 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.add"; rfl) | (trace "PRV-S2 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.add"; delta FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.M31.add FIn_WeightsExtract.field.M31.add; try simp only [PRVEq.C05_F01.FIn_WeightsFuns_h1.field.P]; try rfl; done)
#print axioms PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.add

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.sub : @FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.M31.sub = @FIn_WeightsExtract.field.M31.sub := by
  first | (trace "PRV-S1 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.sub"; rfl) | (trace "PRV-S2 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.sub"; delta FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.M31.sub FIn_WeightsExtract.field.M31.sub; try simp only [PRVEq.C05_F01.FIn_WeightsFuns_h1.field.P]; try rfl; done)
#print axioms PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.sub

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.mul : @FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.M31.mul = @FIn_WeightsExtract.field.M31.mul := by
  first | (trace "PRV-S1 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.mul"; rfl) | (trace "PRV-S2 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.mul"; delta FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.M31.mul FIn_WeightsExtract.field.M31.mul; try simp only [PRVEq.C05_F01.FIn_WeightsFuns_h1.field.reduce_u64]; try rfl; done)
#print axioms PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.mul

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.reduce_u64 : @FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.M31.reduce_u64 = @FIn_WeightsExtract.field.M31.reduce_u64 := by
  first | (trace "PRV-S1 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.reduce_u64"; rfl) | (trace "PRV-S2 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.reduce_u64"; delta FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.M31.reduce_u64 FIn_WeightsExtract.field.M31.reduce_u64; try simp only [PRVEq.C05_F01.FIn_WeightsFuns_h1.field.reduce_u64]; try rfl; done)
#print axioms PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.reduce_u64

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.double : @FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.M31.double = @FIn_WeightsExtract.field.M31.double := by
  first | (trace "PRV-S1 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.double"; rfl) | (trace "PRV-S2 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.double"; delta FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.M31.double FIn_WeightsExtract.field.M31.double; try simp only [PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.add]; try rfl; done)
#print axioms PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.double

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F01.FIn_WeightsFuns_h1.field.CM31.add : @FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.CM31.add = @FIn_WeightsExtract.field.CM31.add := by
  first | (trace "PRV-S1 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.CM31.add"; rfl) | (trace "PRV-S2 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.CM31.add"; delta FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.CM31.add FIn_WeightsExtract.field.CM31.add; try simp only [PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.add]; try rfl; done)
#print axioms PRVEq.C05_F01.FIn_WeightsFuns_h1.field.CM31.add

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F01.FIn_WeightsFuns_h1.field.CM31.sub : @FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.CM31.sub = @FIn_WeightsExtract.field.CM31.sub := by
  first | (trace "PRV-S1 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.CM31.sub"; rfl) | (trace "PRV-S2 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.CM31.sub"; delta FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.CM31.sub FIn_WeightsExtract.field.CM31.sub; try simp only [PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.sub]; try rfl; done)
#print axioms PRVEq.C05_F01.FIn_WeightsFuns_h1.field.CM31.sub

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F01.FIn_WeightsFuns_h1.field.CM31.mul : @FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.CM31.mul = @FIn_WeightsExtract.field.CM31.mul := by
  first | (trace "PRV-S1 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.CM31.mul"; rfl) | (trace "PRV-S2 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.CM31.mul"; delta FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.CM31.mul FIn_WeightsExtract.field.CM31.mul; try simp only [PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.sub, PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.mul, PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.reduce_u64]; try rfl; done)
#print axioms PRVEq.C05_F01.FIn_WeightsFuns_h1.field.CM31.mul

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F01.FIn_WeightsFuns_h1.field.mul_by_r : @FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.mul_by_r = @FIn_WeightsExtract.field.mul_by_r := by
  first | (trace "PRV-S1 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.mul_by_r"; rfl) | (trace "PRV-S2 PRVEq.C05_F01.FIn_WeightsFuns_h1.field.mul_by_r"; delta FIn_WeightsExtract.PRVFresh_C05_F01_FIn_WeightsFuns_h1.field.mul_by_r FIn_WeightsExtract.field.mul_by_r; try simp only [PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.add, PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.sub, PRVEq.C05_F01.FIn_WeightsFuns_h1.field.M31.double]; try rfl; done)
#print axioms PRVEq.C05_F01.FIn_WeightsFuns_h1.field.mul_by_r


end
end PRVBundle_1
section PRVBundle_2
-- GENERATED by PCQH_gen_equalities.py for gate module NFN_ExtractedGeometry. Statements are against the gate constants of NFN_ExtractedGeometry.
-- fresh emission: PCQH_h07 -> PRVFresh_C05_F02_NFN_ExtractedGeometry_h1; fresh source sha256 d39c7f5a2ffc8998178e222a028e8ab606a5d5432eaa3f3b59935165cd5eb472
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace NEW_GeometryActual
namespace PRVFresh_C05_F02_NFN_ExtractedGeometry_h1
/- PRV constant binding (PCUH, recorded): the fresh emission types the cross-crate constants aspis_core.field.M31.ZERO/ONE as the external
   `Result M31` (FunsExternal_Template); the gate carries the pure constants. These two definitions instantiate the external with the gate
   value. Results that use them are CONDITIONAL_ON_BINDING until the constants' own fresh definition is shown equal. -/
def aspis_core.field.M31.ZERO : Result aspis_core.field.M31 := ok (_root_.NEW_GeometryActual.aspis_core.field.M31.ZERO)
def aspis_core.field.M31.ONE : Result aspis_core.field.M31 := ok (_root_.NEW_GeometryActual.aspis_core.field.M31.ONE)
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



/-- Trait implementation: [core::iter::adapters::map::{impl core::iter::traits::iterator::Iterator<B> for core::iter::adapters::map::Map<I, F>}]
    Source: '/rustc/library/core/src/iter/adapters/map.rs', lines 99:0-101:27
    Name pattern: [core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>] -/
@[reducible]
impl_def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator {B :
  Type} {I : Type} {F : Type} {Clause0_Item : Type} (traitsiteratorIteratorInst
  : core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutFTupleClause0_ItemBInst : core.ops.function.FnMut F
  Clause0_Item B) : core.iter.traits.iterator.Iterator
  (core.iter.adapters.map.Map I F) B := {
  next := core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
    traitsiteratorIteratorInst opsfunctionFnMutFTupleClause0_ItemBInst
}

/-- Trait implementation: [aspis_core::field::{impl core::clone::Clone for aspis_core::field::M31}]
    Source: 'crates/aspis-core/src/field.rs', lines 22:9-22:14
    Name pattern: [core::clone::Clone<aspis_core::field::M31>] -/
@[reducible]
def aspis_core.field.M31.Insts.CoreCloneClone : core.clone.Clone
  aspis_core.field.M31 := {
  clone := aspis_core.field.M31.Insts.CoreCloneClone.clone
}

/-- [aspis_r1_cost_probe::fast_domain::TABLE_A]
    Source: 'crates/aspis-r1-cost-probe/src/fast_domain.rs', lines 13:0-142:2 -/
@[global_simps, irreducible]
def fast_domain.TABLE_A : Array (Std.U32 × Std.U32) 512#usize :=
  Array.make 512#usize [
    (1022251061#u32, 788094511#u32), (788094511#u32, 1125232586#u32),
    (1462922215#u32, 117240331#u32), (117240331#u32, 684561432#u32),
    (479936188#u32, 217587789#u32), (217587789#u32, 1667547459#u32),
    (797223315#u32, 1892184156#u32), (1892184156#u32, 1350260332#u32),
    (1601663285#u32, 2022005567#u32), (2022005567#u32, 545820362#u32),
    (1715132412#u32, 1963268365#u32), (1963268365#u32, 432351235#u32),
    (1329069890#u32, 1640136239#u32), (1640136239#u32, 818413757#u32),
    (1052324090#u32, 1064735370#u32), (1064735370#u32, 1095159557#u32),
    (119109612#u32, 1742172267#u32), (1742172267#u32, 2028374035#u32),
    (1949036272#u32, 2084561085#u32), (2084561085#u32, 198447375#u32),
    (1276985988#u32, 456990464#u32), (456990464#u32, 870497659#u32),
    (818046810#u32, 1849544479#u32), (1849544479#u32, 1329436837#u32),
    (1068288753#u32, 675427495#u32), (675427495#u32, 1079194894#u32),
    (2144102382#u32, 886761621#u32), (886761621#u32, 3381265#u32),
    (1542630618#u32, 1177056098#u32), (1177056098#u32, 604853029#u32),
    (270443035#u32, 1665395253#u32), (1665395253#u32, 1877040612#u32),
    (1319895764#u32, 573785706#u32), (573785706#u32, 827587883#u32),
    (614428895#u32, 566940551#u32), (566940551#u32, 1533054752#u32),
    (1614159808#u32, 1309336248#u32), (1309336248#u32, 533323839#u32),
    (20753985#u32, 1635511764#u32), (1635511764#u32, 2126729662#u32),
    (1685341984#u32, 359481912#u32), (359481912#u32, 462141663#u32),
    (1152154081#u32, 2106306808#u32), (2106306808#u32, 995329566#u32),
    (638582271#u32, 300788326#u32), (300788326#u32, 1508901376#u32),
    (1412610045#u32, 1446210525#u32), (1446210525#u32, 734873602#u32),
    (1747362177#u32, 1031300071#u32), (1031300071#u32, 400121470#u32),
    (45393311#u32, 1630721361#u32), (1630721361#u32, 2102090336#u32),
    (628786761#u32, 140902127#u32), (140902127#u32, 1518696886#u32),
    (1117531616#u32, 1012065003#u32), (1012065003#u32, 1029952031#u32),
    (320524274#u32, 1536842560#u32), (1536842560#u32, 1826959373#u32),
    (362376885#u32, 1168590975#u32), (1168590975#u32, 1785106762#u32),
    (1108016105#u32, 252024370#u32), (252024370#u32, 1039467542#u32),
    (1225642256#u32, 1294224634#u32), (1294224634#u32, 921841391#u32),
    (400584953#u32, 469433912#u32), (469433912#u32, 1746898694#u32),
    (932754395#u32, 1184859162#u32), (1184859162#u32, 1214729252#u32),
    (1636215277#u32, 965201017#u32), (965201017#u32, 511268370#u32),
    (993237774#u32, 289789953#u32), (289789953#u32, 1154245873#u32),
    (1844375598#u32, 1823771499#u32), (1823771499#u32, 303108049#u32),
    (1036868259#u32, 1302232773#u32), (1302232773#u32, 1110615388#u32),
    (1489475671#u32, 1590331411#u32), (1590331411#u32, 658007976#u32),
    (271955858#u32, 2011039234#u32), (2011039234#u32, 1875527789#u32),
    (494932510#u32, 292984488#u32), (292984488#u32, 1652551137#u32),
    (1415786230#u32, 1111815158#u32), (1111815158#u32, 731697417#u32),
    (1150508049#u32, 626837953#u32), (626837953#u32, 996975598#u32),
    (317286896#u32, 920117449#u32), (920117449#u32, 1830196751#u32),
    (1935941148#u32, 1205027416#u32), (1205027416#u32, 211542499#u32),
    (809155383#u32, 303944815#u32), (303944815#u32, 1338328264#u32),
    (541880188#u32, 1280134915#u32), (1280134915#u32, 1605603459#u32),
    (1598024857#u32, 1875094528#u32), (1875094528#u32, 549458790#u32),
    (405858396#u32, 413054922#u32), (413054922#u32, 1741625251#u32),
    (1343434959#u32, 1740046445#u32), (1740046445#u32, 804048688#u32),
    (1697594322#u32, 1318496168#u32), (1318496168#u32, 449889325#u32),
    (1908257733#u32, 904587623#u32), (904587623#u32, 239225914#u32),
    (1569205000#u32, 1460088186#u32), (1460088186#u32, 578278647#u32),
    (742503567#u32, 20511103#u32), (20511103#u32, 1404980080#u32),
    (924436841#u32, 179213100#u32), (179213100#u32, 1223046806#u32),
    (776651208#u32, 1692488596#u32), (1692488596#u32, 1370832439#u32),
    (685109443#u32, 308131929#u32), (308131929#u32, 1462374204#u32),
    (1418607411#u32, 1674242439#u32), (1674242439#u32, 728876236#u32),
    (1831338762#u32, 818744620#u32), (818744620#u32, 316144885#u32),
    (136027637#u32, 84984741#u32), (84984741#u32, 2011456010#u32),
    (832857621#u32, 1800803482#u32), (1800803482#u32, 1314626026#u32),
    (1029184762#u32, 1463990705#u32), (1463990705#u32, 1118298885#u32),
    (1026246497#u32, 462715637#u32), (462715637#u32, 1121237150#u32),
    (1630230719#u32, 432660073#u32), (432660073#u32, 517252928#u32),
    (789199007#u32, 265368403#u32), (265368403#u32, 1358284640#u32),
    (905527003#u32, 2103042246#u32), (2103042246#u32, 1241956644#u32),
    (966963960#u32, 791773240#u32), (791773240#u32, 1180519687#u32),
    (429418708#u32, 1721759118#u32), (1721759118#u32, 1718064939#u32),
    (226919109#u32, 591805476#u32), (591805476#u32, 1920564538#u32),
    (1601482956#u32, 1555011007#u32), (1555011007#u32, 546000691#u32),
    (925678133#u32, 1851895798#u32), (1851895798#u32, 1221805514#u32),
    (890643854#u32, 2061547316#u32), (2061547316#u32, 1256839793#u32),
    (2045776109#u32, 764411913#u32), (764411913#u32, 101707538#u32),
    (142321536#u32, 2005775263#u32), (2005775263#u32, 2005162111#u32),
    (852511271#u32, 383685221#u32), (383685221#u32, 1294972376#u32),
    (1850100142#u32, 606004238#u32), (606004238#u32, 297383505#u32),
    (1988413837#u32, 422428418#u32), (422428418#u32, 159069810#u32),
    (1145573298#u32, 2059018920#u32), (2059018920#u32, 1001910349#u32),
    (1024200565#u32, 2131726269#u32), (2131726269#u32, 1123283082#u32),
    (1335475227#u32, 1076118019#u32), (1076118019#u32, 812008420#u32),
    (430897376#u32, 660937846#u32), (660937846#u32, 1716586271#u32),
    (178995476#u32, 298519990#u32), (298519990#u32, 1968488171#u32),
    (1413092576#u32, 2009537990#u32), (2009537990#u32, 734391071#u32),
    (424922113#u32, 74654605#u32), (74654605#u32, 1722561534#u32),
    (665291814#u32, 184778403#u32), (184778403#u32, 1482191833#u32),
    (90485419#u32, 2034131803#u32), (2034131803#u32, 2056998228#u32),
    (1608154088#u32, 833338502#u32), (833338502#u32, 539329559#u32),
    (473403782#u32, 542036433#u32), (542036433#u32, 1674079865#u32),
    (955512264#u32, 573921543#u32), (573921543#u32, 1191971383#u32),
    (661117737#u32, 832530753#u32), (832530753#u32, 1486365910#u32),
    (251387545#u32, 585003076#u32), (585003076#u32, 1896096102#u32),
    (661565914#u32, 1221956578#u32), (1221956578#u32, 1485917733#u32),
    (420922661#u32, 1190171598#u32), (1190171598#u32, 1726560986#u32),
    (746184711#u32, 1733602777#u32), (1733602777#u32, 1401298936#u32),
    (1717922210#u32, 1653599957#u32), (1653599957#u32, 429561437#u32),
    (742148341#u32, 1117355050#u32), (1117355050#u32, 1405335306#u32),
    (2123635407#u32, 1081507110#u32), (1081507110#u32, 23848240#u32),
    (1274756874#u32, 824918498#u32), (824918498#u32, 872726773#u32),
    (75612694#u32, 638305945#u32), (638305945#u32, 2071870953#u32),
    (1146595981#u32, 37855626#u32), (37855626#u32, 1000887666#u32),
    (1128749075#u32, 1106851245#u32), (1106851245#u32, 1018734572#u32),
    (1189119296#u32, 1858928305#u32), (1858928305#u32, 958364351#u32),
    (1936509027#u32, 329657887#u32), (329657887#u32, 210974620#u32),
    (2067891986#u32, 853385273#u32), (853385273#u32, 79591661#u32),
    (242763393#u32, 80138650#u32), (80138650#u32, 1904720254#u32),
    (202216255#u32, 1166833230#u32), (1166833230#u32, 1945267392#u32),
    (1704605091#u32, 1002003657#u32), (1002003657#u32, 442878556#u32),
    (1228317011#u32, 328390175#u32), (328390175#u32, 919166636#u32),
    (1870718732#u32, 902417887#u32), (902417887#u32, 276764915#u32),
    (1517692234#u32, 1936279112#u32), (1936279112#u32, 629791413#u32),
    (1050410086#u32, 1073301032#u32), (1073301032#u32, 1097073561#u32),
    (558333589#u32, 618725725#u32), (618725725#u32, 1589150058#u32),
    (188438465#u32, 212575099#u32), (212575099#u32, 1959045182#u32),
    (2107512806#u32, 635240816#u32), (635240816#u32, 39970841#u32),
    (1351399750#u32, 1217896196#u32), (1217896196#u32, 796083897#u32),
    (740661540#u32, 1927215114#u32), (1927215114#u32, 1406822107#u32),
    (558100220#u32, 1980501108#u32), (1980501108#u32, 1589383427#u32),
    (2109249359#u32, 247223496#u32), (247223496#u32, 38234288#u32),
    (1012525923#u32, 71691935#u32), (71691935#u32, 1134957724#u32),
    (1828798623#u32, 27117548#u32), (27117548#u32, 318685024#u32),
    (2039959946#u32, 1457037680#u32), (1457037680#u32, 107523701#u32),
    (2038288495#u32, 670227777#u32), (670227777#u32, 109195152#u32),
    (209663158#u32, 168116384#u32), (168116384#u32, 1937820489#u32),
    (984290948#u32, 99941766#u32), (99941766#u32, 1163192699#u32),
    (1252927563#u32, 799345076#u32), (799345076#u32, 894556084#u32),
    (419428947#u32, 1890870518#u32), (1890870518#u32, 1728054700#u32),
    (1157494553#u32, 1817015079#u32), (1817015079#u32, 989989094#u32),
    (891334987#u32, 1040656207#u32), (1040656207#u32, 1256148660#u32),
    (785785922#u32, 1967683322#u32), (1967683322#u32, 1361697725#u32),
    (1302242334#u32, 693913202#u32), (693913202#u32, 845241313#u32),
    (1932511129#u32, 687696804#u32), (687696804#u32, 214972518#u32),
    (429857837#u32, 1376073165#u32), (1376073165#u32, 1717625810#u32),
    (778346524#u32, 2089805548#u32), (2089805548#u32, 1369137123#u32),
    (1132767988#u32, 594038315#u32), (594038315#u32, 1014715659#u32),
    (2078867071#u32, 276497442#u32), (276497442#u32, 68616576#u32),
    (22088804#u32, 47256722#u32), (47256722#u32, 2125394843#u32),
    (2089806413#u32, 155403522#u32), (155403522#u32, 57677234#u32),
    (396887507#u32, 760876211#u32), (760876211#u32, 1750596140#u32),
    (1005915392#u32, 1867478512#u32), (1867478512#u32, 1141568255#u32),
    (1098427204#u32, 880292698#u32), (880292698#u32, 1049056443#u32),
    (10571466#u32, 1530894063#u32), (1530894063#u32, 2136912181#u32),
    (1927076832#u32, 605215390#u32), (605215390#u32, 220406815#u32),
    (1461025413#u32, 1421466600#u32), (1421466600#u32, 686458234#u32),
    (725035983#u32, 816938404#u32), (816938404#u32, 1422447664#u32),
    (381944357#u32, 1303428041#u32), (1303428041#u32, 1765539290#u32),
    (1593271412#u32, 1557280492#u32), (1557280492#u32, 554212235#u32),
    (2095613886#u32, 527857063#u32), (527857063#u32, 51869761#u32),
    (2125667422#u32, 1995711117#u32), (1995711117#u32, 21816225#u32),
    (1589276025#u32, 1583924546#u32), (1583924546#u32, 558207622#u32),
    (425606435#u32, 736395182#u32), (736395182#u32, 1721877212#u32),
    (820025422#u32, 857904003#u32), (857904003#u32, 1327458225#u32),
    (367584259#u32, 2107277889#u32), (2107277889#u32, 1779899388#u32),
    (1845204024#u32, 116979180#u32), (116979180#u32, 302279623#u32),
    (1158837492#u32, 819566845#u32), (819566845#u32, 988646155#u32),
    (1766982315#u32, 596409291#u32), (596409291#u32, 380501332#u32),
    (1060867294#u32, 1016052282#u32), (1016052282#u32, 1086616353#u32),
    (15470579#u32, 1643565293#u32), (1643565293#u32, 2132013068#u32),
    (1886413538#u32, 1618829578#u32), (1618829578#u32, 261070109#u32),
    (1399753701#u32, 1692335411#u32), (1692335411#u32, 747729946#u32),
    (1150072909#u32, 950473072#u32), (950473072#u32, 997410738#u32),
    (894752084#u32, 1749876144#u32), (1749876144#u32, 1252731563#u32),
    (1770167713#u32, 338572024#u32), (338572024#u32, 377315934#u32),
    (1674153723#u32, 1322319557#u32), (1322319557#u32, 473329924#u32),
    (1189130906#u32, 937749255#u32), (937749255#u32, 958352741#u32),
    (406765125#u32, 1121751370#u32), (1121751370#u32, 1740718522#u32),
    (667409179#u32, 1770171037#u32), (1770171037#u32, 1480074468#u32),
    (336549856#u32, 2103544920#u32), (2103544920#u32, 1810933791#u32),
    (1914474864#u32, 440166738#u32), (440166738#u32, 233008783#u32),
    (2003660710#u32, 1164690642#u32), (1164690642#u32, 143822937#u32),
    (440188121#u32, 714460670#u32), (714460670#u32, 1707295526#u32),
    (1894212231#u32, 1899640059#u32), (1899640059#u32, 253271416#u32),
    (1270997537#u32, 1765408850#u32), (1765408850#u32, 876486110#u32),
    (834173210#u32, 2010056637#u32), (2010056637#u32, 1313310437#u32),
    (1080830343#u32, 1196541462#u32), (1196541462#u32, 1066653304#u32),
    (703912353#u32, 1783773358#u32), (1783773358#u32, 1443571294#u32),
    (153621575#u32, 797360221#u32), (797360221#u32, 1993862072#u32),
    (635778846#u32, 1298887220#u32), (1298887220#u32, 1511704801#u32),
    (1420391248#u32, 495658886#u32), (495658886#u32, 727092399#u32),
    (1273099376#u32, 2109025845#u32), (2109025845#u32, 874384271#u32),
    (290670999#u32, 484618707#u32), (484618707#u32, 1856812648#u32),
    (1953093309#u32, 1399852939#u32), (1399852939#u32, 194390338#u32),
    (1931790297#u32, 476503814#u32), (476503814#u32, 215693350#u32),
    (1168611337#u32, 1316554005#u32), (1316554005#u32, 978872310#u32),
    (1318032416#u32, 914753745#u32), (914753745#u32, 829451231#u32),
    (1016770609#u32, 602494260#u32), (602494260#u32, 1130713038#u32),
    (45277316#u32, 1384212302#u32), (1384212302#u32, 2102206331#u32),
    (298013744#u32, 1631477536#u32), (1631477536#u32, 1849469903#u32),
    (1504211713#u32, 91770747#u32), (91770747#u32, 643271934#u32),
    (321646901#u32, 781973549#u32), (781973549#u32, 1825836746#u32),
    (1957773767#u32, 58465136#u32), (58465136#u32, 189709880#u32),
    (838659345#u32, 1494392856#u32), (1494392856#u32, 1308824302#u32),
    (1184172815#u32, 1501800213#u32), (1501800213#u32, 963310832#u32),
    (1421224217#u32, 977701755#u32), (977701755#u32, 726259430#u32),
    (1514835708#u32, 825288080#u32), (825288080#u32, 632647939#u32),
    (963110699#u32, 493845922#u32), (493845922#u32, 1184372948#u32),
    (845600471#u32, 1262183431#u32), (1262183431#u32, 1301883176#u32),
    (779436839#u32, 223436892#u32), (223436892#u32, 1368046808#u32),
    (1371651014#u32, 244997852#u32), (244997852#u32, 775832633#u32),
    (1368395169#u32, 2122900869#u32), (2122900869#u32, 779088478#u32),
    (2039730200#u32, 1811033336#u32), (1811033336#u32, 107753447#u32),
    (162657442#u32, 1560528002#u32), (1560528002#u32, 1984826205#u32),
    (1553098421#u32, 1743803217#u32), (1743803217#u32, 594385226#u32),
    (24486645#u32, 110112918#u32), (110112918#u32, 2122997002#u32),
    (1774553093#u32, 1188070682#u32), (1188070682#u32, 372930554#u32),
    (534092016#u32, 1184883641#u32), (1184883641#u32, 1613391631#u32),
    (1045751413#u32, 627353290#u32), (627353290#u32, 1101732234#u32),
    (903868214#u32, 1028549284#u32), (1028549284#u32, 1243615433#u32),
    (753759022#u32, 1035405166#u32), (1035405166#u32, 1393724625#u32),
    (1952803077#u32, 464954162#u32), (464954162#u32, 194680570#u32),
    (102502428#u32, 487991121#u32), (487991121#u32, 2044981219#u32),
    (286638124#u32, 1789802823#u32), (1789802823#u32, 1860845523#u32),
    (2092563395#u32, 1015929240#u32), (1015929240#u32, 54920252#u32),
    (324159263#u32, 1533483219#u32), (1533483219#u32, 1823324384#u32),
    (804875961#u32, 1759135764#u32), (1759135764#u32, 1342607686#u32),
    (706014569#u32, 1757890570#u32), (1757890570#u32, 1441469078#u32),
    (448402140#u32, 760266418#u32), (760266418#u32, 1699081507#u32),
    (375974868#u32, 1233265083#u32), (1233265083#u32, 1771508779#u32),
    (113762283#u32, 452178713#u32), (452178713#u32, 2033721364#u32),
    (931200852#u32, 642566420#u32), (642566420#u32, 1216282795#u32),
    (1681153485#u32, 1692397259#u32), (1692397259#u32, 466330162#u32),
    (285193818#u32, 765163688#u32), (765163688#u32, 1862289829#u32),
    (394346139#u32, 1629953179#u32), (1629953179#u32, 1753137508#u32),
    (1937755996#u32, 1620967529#u32), (1620967529#u32, 209727651#u32),
    (1742951453#u32, 411462942#u32), (411462942#u32, 404532194#u32),
    (300510473#u32, 181714998#u32), (181714998#u32, 1846973174#u32),
    (379559102#u32, 697727211#u32), (697727211#u32, 1767924545#u32),
    (1556533402#u32, 2005793122#u32), (2005793122#u32, 590950245#u32),
    (1694422100#u32, 342104775#u32), (342104775#u32, 453061547#u32),
    (512321057#u32, 1271549173#u32), (1271549173#u32, 1635162590#u32),
    (1502308947#u32, 1936338240#u32), (1936338240#u32, 645174700#u32),
    (1988815881#u32, 645751943#u32), (645751943#u32, 158667766#u32),
    (675847432#u32, 1010741234#u32), (1010741234#u32, 1471636215#u32),
    (501721213#u32, 24836471#u32), (24836471#u32, 1645762434#u32),
    (1358569314#u32, 679273363#u32), (679273363#u32, 788914333#u32),
    (1484722465#u32, 1078988777#u32), (1078988777#u32, 662761182#u32),
    (277190863#u32, 2137253840#u32), (2137253840#u32, 1870292784#u32),
    (816500702#u32, 1764869715#u32), (1764869715#u32, 1330982945#u32),
    (1259936220#u32, 2067445894#u32), (2067445894#u32, 887547427#u32),
    (1513273850#u32, 1722220683#u32), (1722220683#u32, 634209797#u32),
    (1564688601#u32, 591957108#u32), (591957108#u32, 582795046#u32),
    (1529521733#u32, 1200601350#u32), (1200601350#u32, 617961914#u32),
    (799417018#u32, 157314149#u32), (157314149#u32, 1348066629#u32),
    (1811854824#u32, 734127761#u32), (734127761#u32, 335628823#u32),
    (1312626624#u32, 408174531#u32), (408174531#u32, 834857023#u32),
    (388664435#u32, 1700426073#u32), (1700426073#u32, 1758819212#u32),
    (2129034372#u32, 1920159279#u32), (1920159279#u32, 18449275#u32),
    (1031337775#u32, 1391460640#u32), (1391460640#u32, 1116145872#u32),
    (2083000424#u32, 83400055#u32), (83400055#u32, 64483223#u32),
    (1755212887#u32, 1545248590#u32), (1545248590#u32, 392270760#u32),
    (97731769#u32, 427520892#u32), (427520892#u32, 2049751878#u32),
    (1461518819#u32, 1258709018#u32), (1258709018#u32, 685964828#u32),
    (822026787#u32, 790328297#u32), (790328297#u32, 1325456860#u32),
    (1887931203#u32, 983768063#u32), (983768063#u32, 259552444#u32),
    (1403104042#u32, 1214106139#u32), (1214106139#u32, 744379605#u32),
    (162197904#u32, 1576977305#u32), (1576977305#u32, 1985285743#u32),
    (1519708073#u32, 1761924179#u32), (1761924179#u32, 627775574#u32)
    ]

/-- [aspis_r1_cost_probe::fast_domain::TABLE_B]
    Source: 'crates/aspis-r1-cost-probe/src/fast_domain.rs', lines 144:0-273:2 -/
@[global_simps, irreducible]
def fast_domain.TABLE_B : Array (Std.U32 × Std.U32) 512#usize :=
  Array.make 512#usize [
    (1#u32, 0#u32), (996212859#u32, 1140996376#u32), (2015554631#u32,
    1088093947#u32), (816867225#u32, 1001272228#u32), (1420207432#u32,
    2023238517#u32), (816861480#u32, 962195439#u32), (1720479643#u32,
    177413607#u32), (451378731#u32, 1322552846#u32), (1330239767#u32,
    1446369578#u32), (829529542#u32, 1666749290#u32), (1801405099#u32,
    774845311#u32), (1643336673#u32, 2137148295#u32), (113986326#u32,
    1659849761#u32), (754227675#u32, 49211602#u32), (1719877370#u32,
    1305056920#u32), (124061924#u32, 222841901#u32), (1543902459#u32,
    1632329423#u32), (1497033183#u32, 266384758#u32), (238192698#u32,
    21195821#u32), (1718190259#u32, 219728259#u32), (837291277#u32,
    535367851#u32), (28838794#u32, 517661087#u32), (1008640538#u32,
    1400738499#u32), (18889267#u32, 303036586#u32), (1338697498#u32,
    1881711368#u32), (1486319117#u32, 1051308334#u32), (57413392#u32,
    1672717428#u32), (1698380290#u32, 1660014787#u32), (1128628559#u32,
    487113817#u32), (1021297342#u32, 1410478134#u32), (36983955#u32,
    1951442989#u32), (498386322#u32, 1121034294#u32), (1389168750#u32,
    838891026#u32), (1636834739#u32, 1597012617#u32), (1454515876#u32,
    223346768#u32), (1756352277#u32, 1351837341#u32), (240698073#u32,
    476721530#u32), (427864406#u32, 1584676261#u32), (185070104#u32,
    2052638160#u32), (1275605666#u32, 2095784385#u32), (296310565#u32,
    109983397#u32), (72206514#u32, 1289188236#u32), (709836333#u32,
    1607887694#u32), (1513780754#u32, 2116268837#u32), (472230981#u32,
    1127178204#u32), (337258740#u32, 799789868#u32), (954563443#u32,
    1672118401#u32), (1873486026#u32, 204075296#u32), (13191618#u32,
    303576968#u32), (1514546700#u32, 482975034#u32), (1820378488#u32,
    1427649814#u32), (20135698#u32, 907128133#u32), (1363572456#u32,
    1209117074#u32), (1184836041#u32, 810606909#u32), (483972604#u32,
    51373831#u32), (309323555#u32, 1207665785#u32), (1577483195#u32,
    846841358#u32), (472215603#u32, 885906123#u32), (1804344690#u32,
    999799715#u32), (175617284#u32, 1795732353#u32), (389608651#u32,
    1555639321#u32), (594200728#u32, 1849269846#u32), (329547558#u32,
    1589038929#u32), (2118815938#u32, 2129511119#u32), (438833264#u32,
    1327019128#u32), (1247546638#u32, 2100838754#u32), (287625694#u32,
    714961257#u32), (155805646#u32, 741953977#u32), (694768587#u32,
    1335510377#u32), (414447487#u32, 1660191568#u32), (1684659278#u32,
    1370520300#u32), (467042048#u32, 2131513571#u32), (1384581133#u32,
    347627210#u32), (1780251437#u32, 1948453877#u32), (1421431969#u32,
    974095169#u32), (961627178#u32, 109177970#u32), (1971845238#u32,
    153904061#u32), (1188557366#u32, 413281552#u32), (1923810989#u32,
    1272366406#u32), (2063888815#u32, 129056561#u32), (1635360495#u32,
    1075839836#u32), (330063644#u32, 208626297#u32), (116111969#u32,
    557501350#u32), (1516934575#u32, 1368952111#u32), (2128165408#u32,
    1866558246#u32), (1794178592#u32, 2103779454#u32), (720638041#u32,
    1133563860#u32), (1149377722#u32, 1799983014#u32), (1004021208#u32,
    1870425365#u32), (706427304#u32, 2023867009#u32), (991418403#u32,
    1480232698#u32), (1912203537#u32, 1288850576#u32), (1461783988#u32,
    258760706#u32), (1321308009#u32, 1742025967#u32), (913493534#u32,
    2126309379#u32), (1963867290#u32, 360941673#u32), (377761958#u32,
    572545120#u32), (1665396419#u32, 574316292#u32), (373302001#u32,
    1507699234#u32), (801595255#u32, 1469213224#u32), (2051626085#u32,
    490550043#u32), (996029127#u32, 950036227#u32), (1288641239#u32,
    397886040#u32), (1264385016#u32, 642191549#u32), (324121113#u32,
    147452506#u32), (1953213394#u32, 1643851743#u32), (1002266725#u32,
    1988311862#u32), (991463235#u32, 37546859#u32), (1174950059#u32,
    1819822737#u32), (2040633711#u32, 425180892#u32), (213923363#u32,
    1047884791#u32), (328526853#u32, 975070234#u32), (1825664712#u32,
    501661179#u32), (656109024#u32, 1300585869#u32), (1145588529#u32,
    205357607#u32), (2020371461#u32, 1932572291#u32), (1466126871#u32,
    410615561#u32), (1161400406#u32, 1079422807#u32), (1209061891#u32,
    111843040#u32), (952468088#u32, 412399546#u32), (640220223#u32,
    1154724018#u32), (471738157#u32, 668712505#u32), (1791257284#u32,
    457765379#u32), (317467001#u32, 1766420009#u32), (1581002989#u32,
    970103636#u32), (632980202#u32, 1582071541#u32), (88625828#u32,
    522726826#u32), (914753278#u32, 1399904526#u32), (1799120754#u32,
    343598868#u32), (1039404017#u32, 1538341569#u32), (666420564#u32,
    2135132831#u32), (1006212893#u32, 1489058627#u32), (844712212#u32,
    1454882131#u32), (1438323515#u32, 1182923843#u32), (292417279#u32,
    377436135#u32), (1952780205#u32, 81555357#u32), (521340221#u32,
    1824173925#u32), (1485690416#u32, 559378410#u32), (1714778873#u32,
    1735902582#u32), (1180311432#u32, 639492535#u32), (245650224#u32,
    1174726897#u32), (25525334#u32, 2000505072#u32), (1606261854#u32,
    1606869623#u32), (1061095678#u32, 38145073#u32), (124482577#u32,
    226221110#u32), (172504864#u32, 1916272282#u32), (1564877543#u32,
    99597748#u32), (876115079#u32, 1775942790#u32), (530115096#u32,
    90442098#u32), (1392272834#u32, 993120013#u32), (399207028#u32,
    155898355#u32), (1327578729#u32, 1084731515#u32), (607954189#u32,
    1091734815#u32), (1323669817#u32, 933421634#u32), (1478673705#u32,
    1008068784#u32), (1962335487#u32, 1399131158#u32), (1055871441#u32,
    345775465#u32), (711647904#u32, 1091839298#u32), (881168337#u32,
    157473534#u32), (1723511612#u32, 1949091952#u32), (263253631#u32,
    1948074535#u32), (804296458#u32, 213396278#u32), (153716819#u32,
    2054656334#u32), (2104095544#u32, 1435777142#u32), (1479292912#u32,
    403634516#u32), (565878948#u32, 1786880501#u32), (682480399#u32,
    799350698#u32), (1340472519#u32, 1675598842#u32), (735504938#u32,
    198004457#u32), (848969192#u32, 1414511411#u32), (2083960347#u32,
    2126322313#u32), (1209545065#u32, 1852982367#u32), (386684296#u32,
    1363813538#u32), (1083568418#u32, 725197280#u32), (1439180125#u32,
    915904269#u32), (1480502711#u32, 1450760425#u32), (1488671228#u32,
    939868393#u32), (1982402#u32, 431614399#u32), (1542296538#u32,
    1163978019#u32), (1244152270#u32, 498961107#u32), (1362074261#u32,
    2047718881#u32), (563752921#u32, 1285853654#u32), (1834599352#u32,
    1895440138#u32), (1662799443#u32, 1810348412#u32), (474711937#u32,
    1020011657#u32), (1134947640#u32, 394118266#u32), (1739468984#u32,
    977169647#u32), (227977990#u32, 1816535211#u32), (836848068#u32,
    529120781#u32), (210740911#u32, 1280364462#u32), (581559614#u32,
    117257650#u32), (510094092#u32, 641201894#u32), (503318431#u32,
    730224775#u32), (1571876055#u32, 1388714234#u32), (1320977789#u32,
    1557620475#u32), (118365627#u32, 1759509849#u32), (795729789#u32,
    119644040#u32), (1386331726#u32, 809207732#u32), (753978456#u32,
    488132937#u32), (662367932#u32, 209372338#u32), (940196297#u32,
    1361581394#u32), (550623242#u32, 753832155#u32), (6376089#u32,
    129509954#u32), (446322859#u32, 1580452721#u32), (1755458239#u32,
    1807540371#u32), (2142868905#u32, 574364801#u32), (1596830861#u32,
    2049034655#u32), (1180209648#u32, 441139635#u32), (338018326#u32,
    944583937#u32), (1306248760#u32, 633800785#u32), (2075561284#u32,
    1405804402#u32), (581907879#u32, 73327176#u32), (2049933380#u32,
    1834113202#u32), (1783858788#u32, 875557115#u32), (1718311009#u32,
    1065402188#u32), (1306014716#u32, 1275597287#u32), (1212070390#u32,
    338345678#u32), (1460417120#u32, 797602420#u32), (1852933947#u32,
    203671172#u32), (1545193553#u32, 364584318#u32), (1776630073#u32,
    603111274#u32), (1049445738#u32, 292144592#u32), (954301220#u32,
    1901175687#u32), (923367882#u32, 1744922936#u32), (347749121#u32,
    1576860820#u32), (1986804722#u32, 1373191730#u32), (1616101075#u32,
    811514491#u32), (147800194#u32, 1069151092#u32), (1565145988#u32,
    1765289675#u32), (365445058#u32, 1099441367#u32), (920245660#u32,
    938576836#u32), (204640856#u32, 2040419027#u32), (1213375404#u32,
    771547637#u32), (2064624001#u32, 245417806#u32), (494233883#u32,
    1403803427#u32), (1661270250#u32, 1697085245#u32), (818224288#u32,
    1972399941#u32), (513998937#u32, 202899553#u32), (1757257503#u32,
    734249953#u32), (1601634968#u32, 1790370824#u32), (1829052821#u32,
    673049321#u32), (1765843037#u32, 2085683345#u32), (1213735332#u32,
    1357695652#u32), (1332929929#u32, 2095879383#u32), (914918274#u32,
    1369105915#u32), (1478304746#u32, 406667278#u32), (919065681#u32,
    1216872295#u32), (1932017562#u32, 1757637245#u32), (44588143#u32,
    2058311453#u32), (888152082#u32, 1321895104#u32), (1408222478#u32,
    1721187542#u32), (210392081#u32, 157752587#u32), (1444319707#u32,
    1095294811#u32), (1540140142#u32, 751979754#u32), (570004307#u32,
    1164891669#u32), (1090698404#u32, 2001864991#u32), (595037635#u32,
    2111542451#u32), (433157739#u32, 937025459#u32), (100684459#u32,
    1640456458#u32), (1936161103#u32, 1911011743#u32), (2008329732#u32,
    1737289791#u32), (748970643#u32, 485565246#u32), (1220431105#u32,
    100455014#u32), (1661468032#u32, 1401616134#u32), (798338207#u32,
    2110850421#u32), (1219048271#u32, 773733831#u32), (1789955189#u32,
    505997887#u32), (321157045#u32, 133308492#u32), (1819903752#u32,
    1929668715#u32), (354559414#u32, 1412186133#u32), (683528853#u32,
    193776762#u32), (1371420477#u32, 247094679#u32), (1964662320#u32,
    1382435771#u32), (1249682376#u32, 474254021#u32), (150937652#u32,
    383732090#u32), (588173577#u32, 946133187#u32), (1250840269#u32,
    386418603#u32), (122969455#u32, 311337502#u32), (332209582#u32,
    331411357#u32), (2021756148#u32, 85056840#u32), (1631496031#u32,
    481893475#u32), (964719250#u32, 1012108343#u32), (168460970#u32,
    1615303811#u32), (1764389290#u32, 1617898495#u32), (422755315#u32,
    374503008#u32), (1920015819#u32, 2017323756#u32), (719706205#u32,
    1755223690#u32), (1871020210#u32, 2067959207#u32), (1421883301#u32,
    1767600112#u32), (1742158212#u32, 947474543#u32), (848823435#u32,
    1634673682#u32), (47282233#u32, 1973840192#u32), (1318914216#u32,
    1663922738#u32), (500001204#u32, 1350892375#u32), (2079323762#u32,
    1208852267#u32), (1386607805#u32, 2069854787#u32), (729011542#u32,
    952009042#u32), (1995718635#u32, 990602029#u32), (1079208008#u32,
    2008108071#u32), (985150678#u32, 1044660427#u32), (782570832#u32,
    476532960#u32), (649844810#u32, 475157379#u32), (1462196868#u32,
    1013065725#u32), (405825245#u32, 2000126861#u32), (606906923#u32,
    1264738384#u32), (875583808#u32, 1932435950#u32), (1771477961#u32,
    772209956#u32), (1153435498#u32, 735309441#u32), (291679777#u32,
    1578449442#u32), (1036739736#u32, 4090232#u32), (1954195642#u32,
    800757595#u32), (3045475#u32, 162418948#u32), (953139263#u32,
    265503960#u32), (1255153497#u32, 1873206092#u32), (1109468214#u32,
    24685739#u32), (1194288306#u32, 1664016260#u32), (1954241062#u32,
    1820169310#u32), (461636029#u32, 555407991#u32), (878071934#u32,
    497955134#u32), (1274127696#u32, 398642911#u32), (433600440#u32,
    167145119#u32), (257107986#u32, 1260243949#u32), (2117360294#u32,
    299533990#u32), (1968789303#u32, 1889430098#u32), (18918067#u32,
    521344418#u32), (212412059#u32, 1208547549#u32), (526492512#u32,
    1146089824#u32), (1854906262#u32, 225292938#u32), (2001642678#u32,
    1520422911#u32), (1151864086#u32, 1548621786#u32), (1051514954#u32,
    1945490652#u32), (1231259954#u32, 511844620#u32), (1936661821#u32,
    241049853#u32), (54857805#u32, 2021489568#u32), (2138570352#u32,
    385731389#u32), (830229400#u32, 1396231886#u32), (36975016#u32,
    821963373#u32), (110720662#u32, 731152038#u32), (1672578949#u32,
    179250121#u32), (1682843627#u32, 18309514#u32), (183117139#u32,
    65944434#u32), (1584827345#u32, 909175004#u32), (1845239625#u32,
    562344050#u32), (1315215493#u32, 454778943#u32), (1876139646#u32,
    119923533#u32), (750500769#u32, 1547263668#u32), (849384769#u32,
    61803180#u32), (1513012924#u32, 2142060978#u32), (174156438#u32,
    1448257952#u32), (1976764966#u32, 602953694#u32), (1805314849#u32,
    466904232#u32), (963560469#u32, 803989913#u32), (528497962#u32,
    2048433423#u32), (668998651#u32, 249239603#u32), (58617043#u32,
    693726782#u32), (1475204899#u32, 1648029352#u32), (1576856103#u32,
    1461690978#u32), (1488450015#u32, 601243945#u32), (799756877#u32,
    308500462#u32), (571821609#u32, 1489087773#u32), (1029245122#u32,
    1158447597#u32), (1058730422#u32, 1950344727#u32), (1210158521#u32,
    1506582976#u32), (826608058#u32, 2050139532#u32), (2076036242#u32,
    130048956#u32), (185991083#u32, 1518281638#u32), (1797669071#u32,
    2141355836#u32), (413934600#u32, 1586830163#u32), (845078094#u32,
    149898124#u32), (674296139#u32, 317324829#u32), (25637092#u32,
    421692094#u32), (970891652#u32, 610465777#u32), (647843950#u32,
    788293466#u32), (148228362#u32, 590602766#u32), (69829270#u32,
    1352453515#u32), (1683233817#u32, 1287709593#u32), (887385898#u32,
    608769478#u32), (1269707845#u32, 1452388824#u32), (852276839#u32,
    226974950#u32), (412577235#u32, 1997534047#u32), (1615674956#u32,
    1808914239#u32), (406123904#u32, 764760651#u32), (2126452532#u32,
    708823575#u32), (1991612315#u32, 1875574124#u32), (1475016787#u32,
    1876816901#u32), (1065576003#u32, 1260155159#u32), (150344386#u32,
    103390841#u32), (1736259183#u32, 993645757#u32), (458199028#u32,
    2319221#u32), (870734736#u32, 2085864614#u32), (1388011311#u32,
    312501879#u32), (1669933146#u32, 467772885#u32), (957870942#u32,
    905094216#u32), (1326380755#u32, 140779095#u32), (1569000839#u32,
    48016228#u32), (139466273#u32, 1803083243#u32), (1681738638#u32,
    1038838871#u32), (1677449438#u32, 113082240#u32), (1490057922#u32,
    1016920220#u32), (1801577965#u32, 1312472321#u32), (1214106985#u32,
    780900129#u32), (1907575337#u32, 569832496#u32), (582949328#u32,
    603337063#u32), (2009192190#u32, 566186921#u32), (236415000#u32,
    1220441885#u32), (1100966113#u32, 642444966#u32), (2086832175#u32,
    647027993#u32), (442183737#u32, 184219552#u32), (891287480#u32,
    1172290213#u32), (398898618#u32, 2000607785#u32), (991079294#u32,
    1616314544#u32), (641638338#u32, 1769768123#u32), (1085445012#u32,
    1626464664#u32), (1917457045#u32, 820650395#u32), (1885905244#u32,
    1519283397#u32), (2098046315#u32, 239316783#u32), (1984370174#u32,
    548484416#u32), (1760363481#u32, 2129820178#u32), (1997990904#u32,
    355093967#u32), (1980954341#u32, 561676940#u32), (207319829#u32,
    330698049#u32), (480315830#u32, 137067372#u32), (1608197410#u32,
    953495473#u32), (1433755461#u32, 316564196#u32), (591304555#u32,
    68989614#u32), (569540672#u32, 885330917#u32), (865056590#u32,
    1396323689#u32), (237150930#u32, 715611246#u32), (1167250594#u32,
    1854887903#u32), (112696124#u32, 268389163#u32), (719959488#u32,
    88680757#u32), (498135791#u32, 1918711876#u32), (854984042#u32,
    63484416#u32), (512573355#u32, 559650698#u32), (450129036#u32,
    2130393939#u32), (934129539#u32, 1082077994#u32), (787391422#u32,
    234435571#u32), (808165703#u32, 1317710352#u32), (92769725#u32,
    1231653419#u32), (1699669774#u32, 817702196#u32), (1696657789#u32,
    2121958423#u32), (181669902#u32, 1993442275#u32), (1735177288#u32,
    1041858071#u32), (265914936#u32, 748543764#u32), (2077839401#u32,
    709133143#u32), (479770865#u32, 2027287932#u32), (1742529025#u32,
    278083478#u32), (1334313253#u32, 1249554241#u32), (1124768046#u32,
    299494314#u32), (1055409021#u32, 1215994438#u32), (333636023#u32,
    948573238#u32), (548067276#u32, 713948312#u32), (1458581325#u32,
    1279621404#u32), (1873772561#u32, 1110881047#u32), (994459063#u32,
    1883501554#u32), (308028775#u32, 1118600221#u32), (1924483244#u32,
    1528988896#u32), (176039723#u32, 154417691#u32), (841695573#u32,
    113926739#u32), (52691895#u32, 801280851#u32), (1212320872#u32,
    1495300507#u32), (540487422#u32, 1063443989#u32), (1994468584#u32,
    1611997849#u32), (2119188567#u32, 919124989#u32), (1753543609#u32,
    1294275673#u32), (1908790330#u32, 386453773#u32), (1573749961#u32,
    753946855#u32), (305276529#u32, 1041544704#u32), (128738146#u32,
    457848703#u32), (582395095#u32, 1653762059#u32), (1104635206#u32,
    858881536#u32), (1504303166#u32, 365743328#u32), (122809504#u32,
    181977862#u32), (617875881#u32, 1291144021#u32), (895013455#u32,
    284231781#u32), (1880738855#u32, 621634671#u32), (1300871249#u32,
    1490001285#u32), (454136966#u32, 941654637#u32), (277472845#u32,
    620479805#u32), (594888648#u32, 735387713#u32), (1168068815#u32,
    1631133982#u32), (598225672#u32, 477392696#u32), (1272345615#u32,
    2072662117#u32), (1788571406#u32, 979662875#u32), (655623719#u32,
    353143806#u32), (1258493728#u32, 1482265298#u32), (854296756#u32,
    1657148963#u32), (1287455995#u32, 1262269285#u32), (1389630114#u32,
    73256692#u32), (463066423#u32, 383444756#u32), (401706099#u32,
    967129345#u32), (1055629173#u32, 1510653447#u32), (1775957340#u32,
    1042791219#u32), (1767305484#u32, 1767768510#u32), (702523908#u32,
    198087577#u32), (498379185#u32, 365852161#u32), (1029759507#u32,
    977441374#u32), (531874659#u32, 2093948690#u32), (274337143#u32,
    1881376116#u32), (1734948438#u32, 924408729#u32), (875099799#u32,
    1659345298#u32), (1568619121#u32, 824042977#u32), (936298450#u32,
    1105042578#u32), (1577684276#u32, 2022021752#u32), (404074859#u32,
    398369746#u32), (931704942#u32, 1582955093#u32), (18011247#u32,
    565274326#u32), (931164423#u32, 2037669329#u32), (1309629376#u32,
    2080668066#u32), (1286492231#u32, 1508399759#u32), (1807661853#u32,
    544066780#u32), (1942053500#u32, 1814876063#u32)
    ]

/-- [aspis_r1_cost_probe::fast_domain::table_value]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_domain.rs', lines 276:0-278:1 -/
def fast_domain.table_value
  (value : (Std.U32 × Std.U32)) : Result aspis_core.field.CM31 := do
  let (i, i1) := value
  aspis_core.field.CM31.new i i1

/-- [aspis_r1_cost_probe::fast_domain::fibre_point]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_domain.rs', lines 282:0-291:1
    Visibility: public -/
def fast_domain.fibre_point
  (u : aspis_core.r0.domain.FibreIndex) :
  Result (aspis_core.r0.domain.Point aspis_core.field.M31)
  := do
  let index ← aspis_core.r0.domain.FibreIndex.get u
  let i ← lift (index &&& 511#usize)
  let p ← Array.index_usize fast_domain.TABLE_A i
  let left ← fast_domain.table_value p
  let i1 ← lift (Std.Usize.wrapping_shr index 9#i32)
  let p1 ← Array.index_usize fast_domain.TABLE_B i1
  let right ← fast_domain.table_value p1
  let point ← aspis_core.field.CM31.mul left right
  ok { x := point.a, y := point.b }

/-- [aspis_r1_cost_probe::fast_domain::line_node]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_domain.rs', lines 295:0-299:1
    Visibility: public -/
def fast_domain.line_node
  (u : aspis_core.r0.domain.FibreIndex) : Result aspis_core.field.M31 := do
  let p ← fast_domain.fibre_point u
  let square ← aspis_core.field.M31.mul p.x p.x
  let m ← aspis_core.field.M31.double square
  let m1 ← aspis_core.field.M31.ONE
  aspis_core.field.M31.sub m m1

/-- [aspis_r1_cost_probe::verifier::batch_prefix_products]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 138:4-143:5 -/
def verifier.batch_prefix_products_loop.body
  (flat : Slice aspis_core.field.M31)
  (prefixes : alloc.vec.Vec aspis_core.field.M31)
  (product : aspis_core.field.M31) (index : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.M31) ×
    aspis_core.field.M31 × Std.Usize) ((alloc.vec.Vec aspis_core.field.M31) ×
    aspis_core.field.M31))
  := do
  let i := Slice.len flat
  if index < i
  then
    let value ← Slice.index_usize flat index
    let prefixes1 ← alloc.vec.Vec.push prefixes product
    let product1 ← aspis_core.field.M31.mul product value
    let index1 ← lift (Std.Usize.wrapping_add index 1#usize)
    ok (cont (prefixes1, product1, index1))
  else ok (done (prefixes, product))

/-- [aspis_r1_cost_probe::verifier::batch_prefix_products]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 138:4-143:5 -/
def verifier.batch_prefix_products_loop
  (flat : Slice aspis_core.field.M31)
  (prefixes : alloc.vec.Vec aspis_core.field.M31)
  (product : aspis_core.field.M31) (index : Std.Usize) :
  Result ((alloc.vec.Vec aspis_core.field.M31) × aspis_core.field.M31)
  := do
  loop
    (fun (prefixes1, product1, index1) =>
      verifier.batch_prefix_products_loop.body flat prefixes1 product1 index1)
    (prefixes, product, index)

/-- [aspis_r1_cost_probe::verifier::batch_prefix_products]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 134:0-145:1 -/
def verifier.batch_prefix_products
  (flat : Slice aspis_core.field.M31) :
  Result ((alloc.vec.Vec aspis_core.field.M31) × aspis_core.field.M31)
  := do
  let i := Slice.len flat
  let prefixes := alloc.vec.Vec.with_capacity aspis_core.field.M31 i
  let product ← aspis_core.field.M31.ONE
  verifier.batch_prefix_products_loop flat prefixes product 0#usize

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::closure<'_0, '_1>}::call_mut]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:74-175:96 -/
def
  verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
  (c : verifier.QueryGeometry.for_range.closure_4.closure)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.M31 ×
    verifier.QueryGeometry.for_range.closure_4.closure)
  := do
  let (v, i) := c
  let i1 ← lift (Std.Usize.wrapping_mul 5#usize i)
  let i2 ← lift (Std.Usize.wrapping_add i1 tupled_args)
  let m ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      aspis_core.field.M31) v i2
  ok (m, c)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::closure<'_0, '_1>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:74-175:96 -/
def
  verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
  (c : verifier.QueryGeometry.for_range.closure_4.closure) (i : Std.Usize) :
  Result aspis_core.field.M31
  := do
  let (m, _) ←
    verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      c i
  ok m

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::closure<'_0, '_1>}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:74-175:96 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure_4.closure
  Std.Usize aspis_core.field.M31 := {
  call_once :=
    verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
}

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::closure<'_0, '_1>}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:74-175:96 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31
  : core.ops.function.FnMut verifier.QueryGeometry.for_range.closure_4.closure
  Std.Usize aspis_core.field.M31 := {
  FnOnceInst :=
    verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  call_mut :=
    verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
}

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnMut<(usize,), [aspis_core::field::M31; 5usize]> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4<'_0>}::call_mut]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:50-175:97 -/
def
  verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut
  (c : verifier.QueryGeometry.for_range.closure_4) (tupled_args : Std.Usize) :
  Result ((Array aspis_core.field.M31 5#usize) ×
    verifier.QueryGeometry.for_range.closure_4)
  := do
  let a ←
    core.array.from_fn 5#usize
      verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31
      (c, tupled_args)
  ok (a, c)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(usize,), [aspis_core::field::M31; 5usize]> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4<'_0>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:50-175:97 -/
def
  verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once
  (c : verifier.QueryGeometry.for_range.closure_4) (i : Std.Usize) :
  Result (Array aspis_core.field.M31 5#usize)
  := do
  let (a, _) ←
    verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut
      c i
  ok a

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(usize,), [aspis_core::field::M31; 5usize]> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4<'_0>}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:50-175:97 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure_4
  Std.Usize (Array aspis_core.field.M31 5#usize) := {
  call_once :=
    verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once
}

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnMut<(usize,), [aspis_core::field::M31; 5usize]> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4<'_0>}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:50-175:97 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315
  : core.ops.function.FnMut verifier.QueryGeometry.for_range.closure_4
  Std.Usize (Array aspis_core.field.M31 5#usize) := {
  FnOnceInst :=
    verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315
  call_mut :=
    verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut
}

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnMut<(&'_ aspis_core::field::M31,), bool> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#3}::call_mut]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 160:33-160:49 -/
def
  verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut
  (c : verifier.QueryGeometry.for_range.closure_3)
  (tupled_args : aspis_core.field.M31) :
  Result (Bool × verifier.QueryGeometry.for_range.closure_3)
  := do
  let m ← aspis_core.field.M31.ZERO
  let b ← aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq tupled_args m
  ok (b, c)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(&'_ aspis_core::field::M31,), bool> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#3}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 160:33-160:49 -/
def
  verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once
  (c : verifier.QueryGeometry.for_range.closure_3) (m : aspis_core.field.M31) :
  Result Bool
  := do
  let (b, _) ←
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut
      c m
  ok b

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(&'_ aspis_core::field::M31,), bool> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#3}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 160:33-160:49 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure_3
  aspis_core.field.M31 Bool := {
  call_once :=
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once
}

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnMut<(&'_ aspis_core::field::M31,), bool> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#3}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 160:33-160:49 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool
  : core.ops.function.FnMut verifier.QueryGeometry.for_range.closure_3
  aspis_core.field.M31 Bool := {
  FnOnceInst :=
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool
  call_mut :=
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut
}

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#2}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 157:94-157:109 -/
def
  verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  (c : verifier.QueryGeometry.for_range.closure_2)
  (tupled_args : aspis_core.r0.Error) :
  Result verifier.Error
  := do
  ok verifier.Error.Query

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#2}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 157:94-157:109 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure_2
  aspis_core.r0.Error verifier.Error := {
  call_once :=
    verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
}

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#1}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 156:92-156:107 -/
def
  verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  (c : verifier.QueryGeometry.for_range.closure_1)
  (tupled_args : aspis_core.r0.Error) :
  Result verifier.Error
  := do
  ok verifier.Error.Query

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#1}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 156:92-156:107 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure_1
  aspis_core.r0.Error verifier.Error := {
  call_once :=
    verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
}

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 154:57-154:72 -/
def
  verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  (c : verifier.QueryGeometry.for_range.closure)
  (tupled_args : aspis_core.r0.Error) :
  Result verifier.Error
  := do
  ok verifier.Error.Query

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 154:57-154:72 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure
  aspis_core.r0.Error verifier.Error := {
  call_once :=
    verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
}

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range]: loop body 1:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 171:8-174:9 -/
def verifier.QueryGeometry.for_range_loop0_loop0.body
  (flat : alloc.vec.Vec aspis_core.field.M31)
  (prefixes : alloc.vec.Vec aspis_core.field.M31)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (suffix_inverse : aspis_core.field.M31)
  (flat_inverse : alloc.vec.Vec aspis_core.field.M31) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.Usize)) × aspis_core.field.M31 × (alloc.vec.Vec
    aspis_core.field.M31)) (alloc.vec.Vec aspis_core.field.M31))
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done flat_inverse)
  | some i =>
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) prefixes i
    let m1 ← aspis_core.field.M31.mul suffix_inverse m
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverse i
    let flat_inverse1 := index_mut_back m1
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat i
    let suffix_inverse1 ← aspis_core.field.M31.mul suffix_inverse m2
    ok (cont (iter1, suffix_inverse1, flat_inverse1))

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range]: loop 1:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 171:8-174:9 -/
def verifier.QueryGeometry.for_range_loop0_loop0
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (flat : alloc.vec.Vec aspis_core.field.M31)
  (prefixes : alloc.vec.Vec aspis_core.field.M31)
  (suffix_inverse : aspis_core.field.M31)
  (flat_inverse : alloc.vec.Vec aspis_core.field.M31) :
  Result (alloc.vec.Vec aspis_core.field.M31)
  := do
  loop
    (fun (iter1, suffix_inverse1, flat_inverse1) =>
      verifier.QueryGeometry.for_range_loop0_loop0.body flat prefixes iter1
      suffix_inverse1 flat_inverse1)
    (iter, suffix_inverse, flat_inverse)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 152:8-177:5 -/
def verifier.QueryGeometry.for_range_loop0.body
  (start : Std.Usize) (iter : core.slice.iter.Iter Std.U32)
  (line_z_values : alloc.vec.Vec aspis_core.field.M31)
  (flat : alloc.vec.Vec aspis_core.field.M31) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U32) × (alloc.vec.Vec
    aspis_core.field.M31) × (alloc.vec.Vec aspis_core.field.M31))
    (core.result.Result verifier.QueryGeometry verifier.Error))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none =>
    let b ← alloc.vec.Vec.is_empty Global flat
    if b
    then
      ok (done (core.result.Result.Ok
        {
          start,
          inverses := (alloc.vec.Vec.new (Array aspis_core.field.M31 5#usize)),
          line_z := line_z_values
        }))
    else
      let s := alloc.vec.Vec.deref flat
      let (prefixes, product) ← verifier.batch_prefix_products s
      let suffix_inverse ← aspis_core.field.M31.inv product
      let i := alloc.vec.Vec.len flat
      let flat_inverse := alloc.vec.Vec.with_capacity aspis_core.field.M31 i
      let i1 := alloc.vec.Vec.len flat
      let m ← aspis_core.field.M31.ZERO
      let flat_inverse1 ←
        alloc.vec.Vec.resize aspis_core.field.M31.Insts.CoreCloneClone
          flat_inverse i1 m
      let i2 := alloc.vec.Vec.len flat
      let iter2 ←
        core.iter.traits.iterator.Iterator.rev.trait_default
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize) { start := 0#usize, «end» := i2 }
      let flat_inverse2 ←
        verifier.QueryGeometry.for_range_loop0_loop0 iter2 flat prefixes
          suffix_inverse flat_inverse1
      let i3 := alloc.vec.Vec.len line_z_values
      let m1 ←
        core.iter.traits.iterator.Iterator.map.default
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315
          { start := 0#usize, «end» := i3 } flat_inverse2
      let inverses ←
        core.iter.traits.iterator.Iterator.collect.default
          (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315)
          (core.iter.traits.collect.FromIteratorVec (Array aspis_core.field.M31
          5#usize)) m1
      ok (done (core.result.Result.Ok
        { start, inverses, line_z := line_z_values }))
  | some query =>
    let u ← lift (UScalar.cast .Usize query)
    let r ← aspis_core.r0.domain.FibreIndex.new u
    let r1 ←
      core.result.Result.map_err
        verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
        r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let p ← fast_domain.fibre_point val
      let i ← u / 4#usize
      let i1 ← lift (Std.Usize.wrapping_mul i 4#usize)
      let r2 ← aspis_core.r0.domain.FibreIndex.new i1
      let r3 ←
        core.result.Result.map_err
          verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
          r2 ()
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let line_x ← fast_domain.line_node val1
        let i2 ← lift (Std.Usize.wrapping_mul i 4#usize)
        let i3 ← lift (Std.Usize.wrapping_add i2 3#usize)
        let r4 ← aspis_core.r0.domain.FibreIndex.new i3
        let r5 ←
          core.result.Result.map_err
            verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError
            r4 ()
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r5
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let line_y ← fast_domain.line_node val2
          let m ← aspis_core.field.M31.mul line_x line_x
          let m1 ← aspis_core.field.M31.double m
          let m2 ← aspis_core.field.M31.ONE
          let line_z ← aspis_core.field.M31.sub m1 m2
          let s ←
            lift (Array.to_slice
              (Array.make 5#usize [ p.x, p.y, line_x, line_y, line_z ]))
          let i4 ← core.slice.Slice.iter s
          let (b, _) ←
            core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
              verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool
              i4 ()
          if b
          then ok (done (core.result.Result.Err verifier.Error.Query))
          else
            let s1 ←
              lift (Array.to_slice
                (Array.make 5#usize [ p.x, p.y, line_x, line_y, line_z ]))
            let flat1 ←
              alloc.vec.Vec.extend_from_slice
                aspis_core.field.M31.Insts.CoreCloneClone flat s1
            let line_z_values1 ← alloc.vec.Vec.push line_z_values line_z
            ok (cont (iter1, line_z_values1, flat1))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r6 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              verifier.QueryGeometry (core.convert.FromSame verifier.Error)
              residual
          ok (done r6)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r4 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            verifier.QueryGeometry (core.convert.FromSame verifier.Error)
            residual
        ok (done r4)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          verifier.QueryGeometry (core.convert.FromSame verifier.Error)
          residual
      ok (done r2)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 152:8-177:5 -/
def verifier.QueryGeometry.for_range_loop0
  (iter : core.slice.iter.Iter Std.U32) (start : Std.Usize)
  (line_z_values : alloc.vec.Vec aspis_core.field.M31)
  (flat : alloc.vec.Vec aspis_core.field.M31) :
  Result (core.result.Result verifier.QueryGeometry verifier.Error)
  := do
  loop
    (fun (iter1, line_z_values1, flat1) =>
      verifier.QueryGeometry.for_range_loop0.body start iter1 line_z_values1
      flat1)
    (iter, line_z_values, flat)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 148:4-177:5 -/
def verifier.QueryGeometry.for_range
  (queries : Array Std.U32 22#usize) (start : Std.Usize) (end1 : Std.Usize) :
  Result (core.result.Result verifier.QueryGeometry verifier.Error)
  := do
  if start > end1
  then ok (core.result.Result.Err verifier.Error.Query)
  else
    let s ← lift (Array.to_slice queries)
    let i := Slice.len s
    if end1 > i
    then ok (core.result.Result.Err verifier.Error.Query)
    else
      let i1 ← lift (Std.Usize.wrapping_sub end1 start)
      let line_z_values := alloc.vec.Vec.with_capacity aspis_core.field.M31 i1
      let i2 ← lift (Std.Usize.wrapping_sub end1 start)
      let i3 ← lift (Std.Usize.wrapping_mul i2 5#usize)
      let flat := alloc.vec.Vec.with_capacity aspis_core.field.M31 i3
      let s1 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U32)) queries
          { start, «end» := end1 }
      let iter ←
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
          s1
      verifier.QueryGeometry.for_range_loop0 iter start line_z_values flat

end PRVFresh_C05_F02_NFN_ExtractedGeometry_h1
end NEW_GeometryActual

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator = @NEW_GeometryActual.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator NEW_GeometryActual.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.aspis_core.field.M31.Insts.CoreCloneClone : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.aspis_core.field.M31.Insts.CoreCloneClone = @NEW_GeometryActual.aspis_core.field.M31.Insts.CoreCloneClone := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.aspis_core.field.M31.Insts.CoreCloneClone"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.aspis_core.field.M31.Insts.CoreCloneClone"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.aspis_core.field.M31.Insts.CoreCloneClone NEW_GeometryActual.aspis_core.field.M31.Insts.CoreCloneClone; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.aspis_core.field.M31.Insts.CoreCloneClone

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.TABLE_A : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.fast_domain.TABLE_A = @NEW_GeometryActual.fast_domain.TABLE_A := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.TABLE_A"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.TABLE_A"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.fast_domain.TABLE_A NEW_GeometryActual.fast_domain.TABLE_A; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.TABLE_A

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.TABLE_B : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.fast_domain.TABLE_B = @NEW_GeometryActual.fast_domain.TABLE_B := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.TABLE_B"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.TABLE_B"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.fast_domain.TABLE_B NEW_GeometryActual.fast_domain.TABLE_B; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.TABLE_B

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.table_value : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.fast_domain.table_value = @NEW_GeometryActual.fast_domain.table_value := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.table_value"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.table_value"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.fast_domain.table_value NEW_GeometryActual.fast_domain.table_value; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.table_value

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.fibre_point : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.fast_domain.fibre_point = @NEW_GeometryActual.fast_domain.fibre_point := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.fibre_point"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.fibre_point"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.fast_domain.fibre_point NEW_GeometryActual.fast_domain.fibre_point; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.TABLE_A, PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.TABLE_B, PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.table_value]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.fibre_point

set_option maxHeartbeats 200000 in
/-- PCUH: CONDITIONAL_ON_BINDING (the fresh namespace binds the external M31.ONE to the gate value, see NFN_prelude). -/
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.line_node : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.fast_domain.line_node = @NEW_GeometryActual.fast_domain.line_node := by
  delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.fast_domain.line_node NEW_GeometryActual.fast_domain.line_node NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.aspis_core.field.M31.ONE
  simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.fibre_point, bind_tc_ok]
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.line_node

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.batch_prefix_products_loop.body : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.batch_prefix_products_loop.body = @NEW_GeometryActual.verifier.batch_prefix_products_loop.body := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.batch_prefix_products_loop.body"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.batch_prefix_products_loop.body"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.batch_prefix_products_loop.body NEW_GeometryActual.verifier.batch_prefix_products_loop.body; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.batch_prefix_products_loop.body

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.batch_prefix_products_loop : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.batch_prefix_products_loop = @NEW_GeometryActual.verifier.batch_prefix_products_loop := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.batch_prefix_products_loop"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.batch_prefix_products_loop"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.batch_prefix_products_loop NEW_GeometryActual.verifier.batch_prefix_products_loop; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.batch_prefix_products_loop.body]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.batch_prefix_products_loop

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.batch_prefix_products : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.batch_prefix_products = @NEW_GeometryActual.verifier.batch_prefix_products := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.batch_prefix_products"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.batch_prefix_products"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.batch_prefix_products NEW_GeometryActual.verifier.batch_prefix_products; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.batch_prefix_products_loop]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.batch_prefix_products

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31 : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31 = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31 := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31 NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut, PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315 : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315 = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315 := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315 NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut, PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut, PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once NEW_GeometryActual.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError = @NEW_GeometryActual.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError NEW_GeometryActual.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0_loop0.body : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0_loop0.body = @NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0.body := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0_loop0.body"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0_loop0.body"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0_loop0.body NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0.body; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0_loop0.body

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0_loop0 : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0_loop0 = @NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0 := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0_loop0"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0_loop0"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0_loop0 NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0_loop0; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0_loop0.body]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0_loop0

set_option maxHeartbeats 400000 in
/-- PCQH: fresh (OFF emission) = gate. The only textual difference is the cross-crate constants M31.ZERO / M31.ONE, typed `Result M31` in the fresh emission and bound in the prelude to the gate values (CONDITIONAL_ON_BINDING upgraded by PRVEq_const_bind of P2h); stage-1/stage-2 `rfl` exhausts the kernel on the unreduced bodies, so the proof is delta + callee rewriting + bind_tc_ok only. -/
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0.body : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0.body = @NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body := by
  delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0.body NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.aspis_core.field.M31.ZERO NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.aspis_core.field.M31.ONE
  simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator, PRVEq.C05_F02.NFN_ExtractedGeometry_h1.aspis_core.field.M31.Insts.CoreCloneClone, PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.fibre_point, PRVEq.C05_F02.NFN_ExtractedGeometry_h1.fast_domain.line_node, PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.batch_prefix_products, PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315, PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool, PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError, PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError, PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError, PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0_loop0, bind_tc_ok]
  rfl
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0.body

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0 : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0 = @NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0 := by
  first | (trace "PRV-S1 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0"; rfl) | (trace "PRV-S2 PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0"; delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0 NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0; try simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0.body]; try rfl; done)
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0

set_option maxHeartbeats 400000 in
/-- PCQH: fresh (OFF) = gate for_range: delta + the proved loop equality (stage-1 rfl exhausts whnf). -/
theorem PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range : @NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range = @NEW_GeometryActual.verifier.QueryGeometry.for_range := by
  delta NEW_GeometryActual.PRVFresh_C05_F02_NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range NEW_GeometryActual.verifier.QueryGeometry.for_range
  simp only [PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range_loop0]
#print axioms PRVEq.C05_F02.NFN_ExtractedGeometry_h1.verifier.QueryGeometry.for_range


end
end PRVBundle_2
section PRVBundle_3
-- GENERATED by PCQH_gen_equalities.py for gate module NFN_ExtractedGeometry. Statements are against the gate constants of NFN_ExtractedGeometry.
-- fresh emission: PCQH_hf1 -> PRVFresh_C05_F03_NFN_ExtractedGeometry_h2; fresh source sha256 f057f4bbf276d4eac13924c7bc52f137e9cee1f0a1e72ff084c579b88c8b0a2c
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace NEW_GeometryActual
namespace PRVFresh_C05_F03_NFN_ExtractedGeometry_h2

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/aspis_core.field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def aspis_core.field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::reduce_u64]:
    Source: 'crates/aspis-core/src/aspis_core.field.rs', lines 31:0-44:1 -/
def aspis_core.field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 aspis_core.field.P)
  let i1 ← lift (x &&& i)
  let i2 ← lift (Std.U64.wrapping_shr x 31#u32)
  let x1 ← lift (Std.U64.wrapping_add i1 i2)
  let i3 ← lift (UScalar.cast .U64 aspis_core.field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← lift (Std.U64.wrapping_shr x1 31#u32)
  let x2 ← lift (Std.U64.wrapping_add i4 i5)
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= aspis_core.field.P
  then ok (Std.U32.wrapping_sub x3 aspis_core.field.P)
  else ok x3

/-- [aspis_core::field::{aspis_core::field::M31}::add]:
    Source: 'crates/aspis-core/src/aspis_core.field.rs', lines 62:4-88:5
    Visibility: public -/
def aspis_core.field.M31.add (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  let s ← lift (Std.U32.wrapping_add self rhs)
  if s >= aspis_core.field.P
  then let s1 ← lift (Std.U32.wrapping_sub s aspis_core.field.P)
       ok s1
  else ok s

/-- [aspis_core::field::{aspis_core::field::M31}::sub]:
    Source: 'crates/aspis-core/src/aspis_core.field.rs', lines 94:4-119:5
    Visibility: public -/
def aspis_core.field.M31.sub (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  let i ← lift (Std.U32.wrapping_add self aspis_core.field.P)
  let s ← lift (Std.U32.wrapping_sub i rhs)
  if s >= aspis_core.field.P
  then let s1 ← lift (Std.U32.wrapping_sub s aspis_core.field.P)
       ok s1
  else ok s

/-- [aspis_core::field::{aspis_core::field::M31}::mul]:
    Source: 'crates/aspis-core/src/aspis_core.field.rs', lines 133:4-137:5
    Visibility: public -/
def aspis_core.field.M31.mul (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← lift (Std.U64.wrapping_mul i i1)
  let i3 ← aspis_core.field.reduce_u64 i2
  ok i3

/-- [aspis_core::field::{aspis_core::field::M31}::reduce_u64]:
    Source: 'crates/aspis-core/src/aspis_core.field.rs', lines 153:4-155:5
    Visibility: public -/
def aspis_core.field.M31.reduce_u64 (value : Std.U64) : Result aspis_core.field.M31 := do
  let i ← aspis_core.field.reduce_u64 value
  ok i

/-- [aspis_core::field::{aspis_core::field::M31}::double]:
    Source: 'crates/aspis-core/src/aspis_core.field.rs', lines 183:4-185:5
    Visibility: public -/
def aspis_core.field.M31.double (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  aspis_core.field.M31.add self self

/-- [aspis_core::field::{aspis_core::field::CM31}::mul]:
    Source: 'crates/aspis-core/src/aspis_core.field.rs', lines 306:4-320:5
    Visibility: public -/
def aspis_core.field.CM31.mul
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  let m0 ← aspis_core.field.M31.mul self.a rhs.a
  let m1 ← aspis_core.field.M31.mul self.b rhs.b
  let i := self.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← lift (Std.U64.wrapping_add i1 i3)
  let i5 := rhs.a
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.b
  let i8 ← lift (core.convert.num.FromU64U32.from i7)
  let i9 ← lift (Std.U64.wrapping_add i6 i8)
  let i10 ← lift (Std.U64.wrapping_mul i4 i9)
  let m2 ← aspis_core.field.M31.reduce_u64 i10
  let m ← aspis_core.field.M31.sub m0 m1
  let m3 ← aspis_core.field.M31.sub m2 m0
  let m4 ← aspis_core.field.M31.sub m3 m1
  ok { a := m, b := m4 }

end PRVFresh_C05_F03_NFN_ExtractedGeometry_h2
end NEW_GeometryActual

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.P : @NEW_GeometryActual.PRVFresh_C05_F03_NFN_ExtractedGeometry_h2.aspis_core.field.P = @NEW_GeometryActual.aspis_core.field.P := by
  first | (trace "PRV-S1 PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.P"; rfl) | (trace "PRV-S2 PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.P"; delta NEW_GeometryActual.PRVFresh_C05_F03_NFN_ExtractedGeometry_h2.aspis_core.field.P NEW_GeometryActual.aspis_core.field.P; try rfl; done)
#print axioms PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.P

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.reduce_u64 : @NEW_GeometryActual.PRVFresh_C05_F03_NFN_ExtractedGeometry_h2.aspis_core.field.reduce_u64 = @NEW_GeometryActual.aspis_core.field.reduce_u64 := by
  first | (trace "PRV-S1 PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.reduce_u64"; rfl) | (trace "PRV-S2 PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.reduce_u64"; delta NEW_GeometryActual.PRVFresh_C05_F03_NFN_ExtractedGeometry_h2.aspis_core.field.reduce_u64 NEW_GeometryActual.aspis_core.field.reduce_u64; try simp only [PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.P]; try rfl; done)
#print axioms PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.reduce_u64

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.add : @NEW_GeometryActual.PRVFresh_C05_F03_NFN_ExtractedGeometry_h2.aspis_core.field.M31.add = @NEW_GeometryActual.aspis_core.field.M31.add := by
  first | (trace "PRV-S1 PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.add"; rfl) | (trace "PRV-S2 PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.add"; delta NEW_GeometryActual.PRVFresh_C05_F03_NFN_ExtractedGeometry_h2.aspis_core.field.M31.add NEW_GeometryActual.aspis_core.field.M31.add; try simp only [PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.P]; try rfl; done)
#print axioms PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.add

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.sub : @NEW_GeometryActual.PRVFresh_C05_F03_NFN_ExtractedGeometry_h2.aspis_core.field.M31.sub = @NEW_GeometryActual.aspis_core.field.M31.sub := by
  first | (trace "PRV-S1 PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.sub"; rfl) | (trace "PRV-S2 PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.sub"; delta NEW_GeometryActual.PRVFresh_C05_F03_NFN_ExtractedGeometry_h2.aspis_core.field.M31.sub NEW_GeometryActual.aspis_core.field.M31.sub; try simp only [PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.P]; try rfl; done)
#print axioms PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.sub

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.mul : @NEW_GeometryActual.PRVFresh_C05_F03_NFN_ExtractedGeometry_h2.aspis_core.field.M31.mul = @NEW_GeometryActual.aspis_core.field.M31.mul := by
  first | (trace "PRV-S1 PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.mul"; rfl) | (trace "PRV-S2 PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.mul"; delta NEW_GeometryActual.PRVFresh_C05_F03_NFN_ExtractedGeometry_h2.aspis_core.field.M31.mul NEW_GeometryActual.aspis_core.field.M31.mul; try simp only [PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.reduce_u64]; try rfl; done)
#print axioms PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.mul

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.reduce_u64 : @NEW_GeometryActual.PRVFresh_C05_F03_NFN_ExtractedGeometry_h2.aspis_core.field.M31.reduce_u64 = @NEW_GeometryActual.aspis_core.field.M31.reduce_u64 := by
  first | (trace "PRV-S1 PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.reduce_u64"; rfl) | (trace "PRV-S2 PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.reduce_u64"; delta NEW_GeometryActual.PRVFresh_C05_F03_NFN_ExtractedGeometry_h2.aspis_core.field.M31.reduce_u64 NEW_GeometryActual.aspis_core.field.M31.reduce_u64; try simp only [PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.reduce_u64]; try rfl; done)
#print axioms PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.reduce_u64

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.double : @NEW_GeometryActual.PRVFresh_C05_F03_NFN_ExtractedGeometry_h2.aspis_core.field.M31.double = @NEW_GeometryActual.aspis_core.field.M31.double := by
  first | (trace "PRV-S1 PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.double"; rfl) | (trace "PRV-S2 PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.double"; delta NEW_GeometryActual.PRVFresh_C05_F03_NFN_ExtractedGeometry_h2.aspis_core.field.M31.double NEW_GeometryActual.aspis_core.field.M31.double; try simp only [PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.add]; try rfl; done)
#print axioms PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.double

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.CM31.mul : @NEW_GeometryActual.PRVFresh_C05_F03_NFN_ExtractedGeometry_h2.aspis_core.field.CM31.mul = @NEW_GeometryActual.aspis_core.field.CM31.mul := by
  first | (trace "PRV-S1 PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.CM31.mul"; rfl) | (trace "PRV-S2 PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.CM31.mul"; delta NEW_GeometryActual.PRVFresh_C05_F03_NFN_ExtractedGeometry_h2.aspis_core.field.CM31.mul NEW_GeometryActual.aspis_core.field.CM31.mul; try simp only [PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.sub, PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.mul, PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.M31.reduce_u64]; try rfl; done)
#print axioms PRVEq.C05_F03.NFN_ExtractedGeometry_h2.aspis_core.field.CM31.mul


end
end PRVBundle_3
section PRVBundle_4
-- GENERATED by PCQH_gen_equalities.py for gate module NJA_CountBody. Statements are against the gate constants of NJA_CountBody.
-- fresh emission: PCQH_h09 -> PRVFresh_C05_F04_NJA_CountBody_h1; fresh source sha256 72c02db1fc538fc0606c0d01a19b9a6c8ee675d45bd4a5eb79eddc656d4616c9
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace NJA_Multiproof
namespace PRVFresh_C05_F04_NJA_CountBody_h1

/-- [aspis_r1_cost_probe::multiproof::{aspis_r1_cost_probe::multiproof::Arity}::bits]:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 32:4-37:5
    Visibility: public -/
def multiproof.Arity.bits (self : multiproof.Arity) : Result Std.U32 := do
  match self with
  | multiproof.Arity.Two => ok 1#u32
  | multiproof.Arity.Eight => ok 3#u32

/-- [aspis_r1_cost_probe::multiproof::{aspis_r1_cost_probe::multiproof::Arity}::width]:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 39:4-41:5
    Visibility: public -/
def multiproof.Arity.width (self : multiproof.Arity) : Result Std.Usize := do
  let i ← multiproof.Arity.bits self
  ok (Std.Usize.wrapping_shl 1#usize i)

/-- [aspis_r1_cost_probe::multiproof::index_at]:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 62:0-64:1 -/
def multiproof.index_at
  (indices : Array Std.U32 16#usize) (index : Std.Usize) : Result Std.U32 := do
  Array.index_usize indices index

/-- [aspis_r1_cost_probe::multiproof::node_count]: loop body 2:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 99:12-101:13
    Visibility: public -/
def multiproof.node_count_loop0_loop0_loop0.body
  (arity : multiproof.Arity) (level : Array Std.U32 16#usize) (n : Std.Usize)
  (parent : Std.U32) (j : Std.Usize) :
  Result (ControlFlow Std.Usize Std.Usize)
  := do
  if j < n
  then
    let i ← multiproof.index_at level j
    let i1 ← multiproof.Arity.bits arity
    let i2 ← lift (Std.U32.wrapping_shr i i1)
    if i2 = parent
    then let j1 ← lift (Std.Usize.wrapping_add j 1#usize)
         ok (cont j1)
    else ok (done j)
  else ok (done j)

/-- [aspis_r1_cost_probe::multiproof::node_count]: loop 2:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 99:12-101:13
    Visibility: public -/
def multiproof.node_count_loop0_loop0_loop0
  (arity : multiproof.Arity) (level : Array Std.U32 16#usize) (n : Std.Usize)
  (parent : Std.U32) (j : Std.Usize) :
  Result Std.Usize
  := do
  loop
    (fun j1 => multiproof.node_count_loop0_loop0_loop0.body arity level n
      parent j1)
    j

/-- [aspis_r1_cost_probe::multiproof::node_count]: loop body 1:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 96:8-106:9
    Visibility: public -/
def multiproof.node_count_loop0_loop0.body
  (arity : multiproof.Arity) (n : Std.Usize) (level : Array Std.U32 16#usize)
  (count : Std.Usize) (w : Std.Usize) (i : Std.Usize) :
  Result (ControlFlow ((Array Std.U32 16#usize) × Std.Usize × Std.Usize ×
    Std.Usize) ((Array Std.U32 16#usize) × Std.Usize × Std.Usize))
  := do
  if i < n
  then
    let i1 ← multiproof.index_at level i
    let i2 ← multiproof.Arity.bits arity
    let parent ← lift (Std.U32.wrapping_shr i1 i2)
    let j ← multiproof.node_count_loop0_loop0_loop0 arity level n parent i
    let i3 ← multiproof.Arity.width arity
    let i4 ← lift (Std.Usize.wrapping_sub j i)
    let i5 ← lift (Std.Usize.wrapping_sub i3 i4)
    let count1 ← lift (Std.Usize.wrapping_add count i5)
    let level1 ← Array.update level w parent
    let w1 ← lift (Std.Usize.wrapping_add w 1#usize)
    ok (cont (level1, count1, w1, j))
  else ok (done (level, count, w))

/-- [aspis_r1_cost_probe::multiproof::node_count]: loop 1:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 96:8-106:9
    Visibility: public -/
def multiproof.node_count_loop0_loop0
  (arity : multiproof.Arity) (level : Array Std.U32 16#usize) (n : Std.Usize)
  (count : Std.Usize) (w : Std.Usize) (i : Std.Usize) :
  Result ((Array Std.U32 16#usize) × Std.Usize × Std.Usize)
  := do
  loop
    (fun (level1, count1, w1, i1) => multiproof.node_count_loop0_loop0.body
      arity n level1 count1 w1 i1)
    (level, count, w, i)

/-- [aspis_r1_cost_probe::multiproof::node_count]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 93:4-108:5
    Visibility: public -/
def multiproof.node_count_loop0.body
  (arity : multiproof.Arity) (iter : core.ops.range.Range Std.U32)
  (level : Array Std.U32 16#usize) (n : Std.Usize) (count : Std.Usize) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × (Array Std.U32
    16#usize) × Std.Usize × Std.Usize) Std.Usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none => ok (done count)
  | some _ =>
    let (level1, count1, w) ←
      multiproof.node_count_loop0_loop0 arity level n count 0#usize 0#usize
    ok (cont (iter1, level1, w, count1))

/-- [aspis_r1_cost_probe::multiproof::node_count]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 93:4-108:5
    Visibility: public -/
def multiproof.node_count_loop0
  (iter : core.ops.range.Range Std.U32) (arity : multiproof.Arity)
  (level : Array Std.U32 16#usize) (n : Std.Usize) (count : Std.Usize) :
  Result Std.Usize
  := do
  loop
    (fun (iter1, level1, n1, count1) => multiproof.node_count_loop0.body arity
      iter1 level1 n1 count1)
    (iter, level, n, count)

end PRVFresh_C05_F04_NJA_CountBody_h1
end NJA_Multiproof

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0_loop0_loop0 : @NJA_Multiproof.PRVFresh_C05_F04_NJA_CountBody_h1.multiproof.node_count_loop0_loop0_loop0 = @NJA_Multiproof.multiproof.node_count_loop0_loop0_loop0 := by
  first | (trace "PRV-S1 PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0_loop0_loop0"; rfl) | (trace "PRV-S2 PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0_loop0_loop0"; delta NJA_Multiproof.PRVFresh_C05_F04_NJA_CountBody_h1.multiproof.node_count_loop0_loop0_loop0 NJA_Multiproof.multiproof.node_count_loop0_loop0_loop0; try rfl; done)
#print axioms PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0_loop0_loop0

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0_loop0.body : @NJA_Multiproof.PRVFresh_C05_F04_NJA_CountBody_h1.multiproof.node_count_loop0_loop0.body = @NJA_Multiproof.multiproof.node_count_loop0_loop0.body := by
  first | (trace "PRV-S1 PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0_loop0.body"; rfl) | (trace "PRV-S2 PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0_loop0.body"; delta NJA_Multiproof.PRVFresh_C05_F04_NJA_CountBody_h1.multiproof.node_count_loop0_loop0.body NJA_Multiproof.multiproof.node_count_loop0_loop0.body; try simp only [PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0_loop0_loop0]; try rfl; done)
#print axioms PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0_loop0.body

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0_loop0 : @NJA_Multiproof.PRVFresh_C05_F04_NJA_CountBody_h1.multiproof.node_count_loop0_loop0 = @NJA_Multiproof.multiproof.node_count_loop0_loop0 := by
  first | (trace "PRV-S1 PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0_loop0"; rfl) | (trace "PRV-S2 PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0_loop0"; delta NJA_Multiproof.PRVFresh_C05_F04_NJA_CountBody_h1.multiproof.node_count_loop0_loop0 NJA_Multiproof.multiproof.node_count_loop0_loop0; try simp only [PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0_loop0.body]; try rfl; done)
#print axioms PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0_loop0

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0.body : @NJA_Multiproof.PRVFresh_C05_F04_NJA_CountBody_h1.multiproof.node_count_loop0.body = @NJA_Multiproof.multiproof.node_count_loop0.body := by
  first | (trace "PRV-S1 PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0.body"; rfl) | (trace "PRV-S2 PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0.body"; delta NJA_Multiproof.PRVFresh_C05_F04_NJA_CountBody_h1.multiproof.node_count_loop0.body NJA_Multiproof.multiproof.node_count_loop0.body; try simp only [PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0_loop0]; try rfl; done)
#print axioms PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0.body

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0 : @NJA_Multiproof.PRVFresh_C05_F04_NJA_CountBody_h1.multiproof.node_count_loop0 = @NJA_Multiproof.multiproof.node_count_loop0 := by
  first | (trace "PRV-S1 PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0"; rfl) | (trace "PRV-S2 PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0"; delta NJA_Multiproof.PRVFresh_C05_F04_NJA_CountBody_h1.multiproof.node_count_loop0 NJA_Multiproof.multiproof.node_count_loop0; try simp only [PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0.body]; try rfl; done)
#print axioms PRVEq.C05_F04.NJA_CountBody_h1.multiproof.node_count_loop0


end
end PRVBundle_4
section PRVBundle_5
-- GENERATED by PCQH_gen_equalities.py for gate module RPz7_FIo_NativeFuns. Statements are against the gate constants of RPz7_FIo_NativeFuns.
-- fresh emission: PCQH_hf1 -> PRVFresh_C05_F05_RPz7_FIo_NativeFuns_h1; fresh source sha256 f057f4bbf276d4eac13924c7bc52f137e9cee1f0a1e72ff084c579b88c8b0a2c
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace FIo_Native
namespace PRVFresh_C05_F05_RPz7_FIo_NativeFuns_h1

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/aspis_core.field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def aspis_core.field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::reduce_u64]:
    Source: 'crates/aspis-core/src/aspis_core.field.rs', lines 31:0-44:1 -/
def aspis_core.field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 aspis_core.field.P)
  let i1 ← lift (x &&& i)
  let i2 ← lift (Std.U64.wrapping_shr x 31#u32)
  let x1 ← lift (Std.U64.wrapping_add i1 i2)
  let i3 ← lift (UScalar.cast .U64 aspis_core.field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← lift (Std.U64.wrapping_shr x1 31#u32)
  let x2 ← lift (Std.U64.wrapping_add i4 i5)
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= aspis_core.field.P
  then ok (Std.U32.wrapping_sub x3 aspis_core.field.P)
  else ok x3

end PRVFresh_C05_F05_RPz7_FIo_NativeFuns_h1
end FIo_Native

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F05.RPz7_FIo_NativeFuns_h1.aspis_core.field.P : @FIo_Native.PRVFresh_C05_F05_RPz7_FIo_NativeFuns_h1.aspis_core.field.P = @FIo_Native.aspis_core.field.P := by
  first | (trace "PRV-S1 PRVEq.C05_F05.RPz7_FIo_NativeFuns_h1.aspis_core.field.P"; rfl) | (trace "PRV-S2 PRVEq.C05_F05.RPz7_FIo_NativeFuns_h1.aspis_core.field.P"; delta FIo_Native.PRVFresh_C05_F05_RPz7_FIo_NativeFuns_h1.aspis_core.field.P FIo_Native.aspis_core.field.P; try rfl; done)
#print axioms PRVEq.C05_F05.RPz7_FIo_NativeFuns_h1.aspis_core.field.P

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F05.RPz7_FIo_NativeFuns_h1.aspis_core.field.reduce_u64 : @FIo_Native.PRVFresh_C05_F05_RPz7_FIo_NativeFuns_h1.aspis_core.field.reduce_u64 = @FIo_Native.aspis_core.field.reduce_u64 := by
  first | (trace "PRV-S1 PRVEq.C05_F05.RPz7_FIo_NativeFuns_h1.aspis_core.field.reduce_u64"; rfl) | (trace "PRV-S2 PRVEq.C05_F05.RPz7_FIo_NativeFuns_h1.aspis_core.field.reduce_u64"; delta FIo_Native.PRVFresh_C05_F05_RPz7_FIo_NativeFuns_h1.aspis_core.field.reduce_u64 FIo_Native.aspis_core.field.reduce_u64; try simp only [PRVEq.C05_F05.RPz7_FIo_NativeFuns_h1.aspis_core.field.P]; try rfl; done)
#print axioms PRVEq.C05_F05.RPz7_FIo_NativeFuns_h1.aspis_core.field.reduce_u64


end
end PRVBundle_5
section PRVBundle_6
open Aeneas Aeneas.Std Result ControlFlow Error
open Lean.Order

namespace PRVC_C05_F06

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
    | (apply PRVC_C05_F06.bind_congr; intro a; try (obtain ⟨_, _⟩ := a); prv_norm)
    | (apply PRVC_C05_F06.ite_congr'; prv_norm)
    | (apply PRVC_C05_F06.dite_congr' <;> intro h)
    | (split <;> prv_norm))))

end PRVC_C05_F06


namespace PRVH_C05_F06

/-- A domain-restricted loop comparison: if two loop bodies agree on an invariant domain that the first body preserves, the loops agree on that domain. -/
theorem loop_le_dom {α β : Type _} (F G : α → Result (ControlFlow α β)) (Inv : α → Prop)
    (hFG : ∀ x, Inv x → F x = G x)
    (hpres : ∀ x x', Inv x → F x = ok (ControlFlow.cont x') → Inv x') :
    ∀ x, Inv x → loop F x ⊑ loop G x := by
  have adm : admissible (fun f : α → Result β => ∀ x, Inv x → f x ⊑ loop G x) := by
    apply admissible_pi_apply (fun x (r : Result β) => Inv x → r ⊑ loop G x)
    intro x
    by_cases h : Inv x
    · simpa [h] using PRVC_C05_F06.adm_le (loop G x)
    · simp [h]
      exact fun c _ _ => trivial
  refine loop.fixpoint_induct F (fun f => ∀ x, Inv x → f x ⊑ loop G x) adm ?_
  intro f hf x hx
  rw [PRVC_C05_F06.loop_unfold G x]
  unfold PRVC_C05_F06.bs
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

end PRVH_C05_F06
#print axioms PRVH_C05_F06.loop_le_dom
#print axioms PRVH_C05_F06.loop_eq_dom
#print axioms PRVH_C05_F06.range_next_end

end PRVBundle_6
section PRVBundle_7
open Aeneas Aeneas.Std Result ControlFlow Error

namespace PRVH_C05_F07

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

end PRVH_C05_F07
#print axioms PRVH_C05_F07.usize_shr_usize
#print axioms PRVH_C05_F07.usize_shl_usize

end PRVBundle_7
section PRVBundle_8
-- GENERATED by PCUA_gen_equalities.py for gate module RPz7_FIo_NativeFuns. Statements are against the gate constants of RPz7_FIo_NativeFuns.
-- fresh emission: PCQ_aspis_r1_cost_probe_candidate -> PRVFresh_C05_F08_RPz7_FIo_NativeFuns; fresh source sha256 f2166b7ff15c5e5ef84f64a77881ffce913b9c4daa6b22066a735c51ab5fb196
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace PRVFresh_C05_F08_RPz7_FIo_NativeFuns
open FIo_Native

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- Trait implementation: [aspis_core::field::wide_exact::{impl core::cmp::PartialEq<aspis_core::field::wide_exact::WideExact> for aspis_core::field::wide_exact::WideExact}]
    Source: 'crates/aspis-core/src/field/wide_exact.rs', lines 27:38-27:47
    Name pattern: [core::cmp::PartialEq<aspis_core::field::wide_exact::WideExact, aspis_core::field::wide_exact::WideExact>] -/
@[reducible]
impl_def aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact
  : core.cmp.PartialEq aspis_core.field.wide_exact.WideExact
  aspis_core.field.wide_exact.WideExact := {
  eq :=
    aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq
  ne := core.cmp.PartialEq.ne.trait_default
    aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact
}
-/

/-- [aspis_r1_cost_probe::compact::FINAL_LEN]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 45:0-45:32
    Visibility: public -/
@[global_simps, irreducible]
 def compact.FINAL_LEN : Std.Usize := 64#usize

/-- [aspis_r1_cost_probe::compact::HEADER]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 26:0-26:29
    Visibility: public -/
@[global_simps, irreducible]
 def compact.HEADER : Std.Usize := 16#usize

/-- [aspis_r1_cost_probe::compact::OFF_SEMANTIC]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 38:0-38:39
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_SEMANTIC : Std.Usize := compact.HEADER

/-- [aspis_r1_cost_probe::compact::SEMANTIC_COMPACT_VALUES]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 33:0-33:72
    Visibility: public -/
@[global_simps, irreducible]
def compact.SEMANTIC_COMPACT_VALUES : Result Std.Usize := do
  let i ← 10#usize * 28#usize
  let i1 ← 1#usize + i
  let i2 ← 87#usize + 29#usize
  let i3 ← i1 + i2
  i3 + 29#usize

/-- [aspis_r1_cost_probe::verifier::SEMANTIC_BYTES]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 8:0-8:43
    Visibility: public -/
@[global_simps, irreducible]
def verifier.SEMANTIC_BYTES : Result Std.Usize := do
  let i ← 29#usize * 32#usize
  12903#usize + i

/-- [aspis_r1_cost_probe::compact::LOGICAL_SEMANTIC]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 31:0-31:68
    Visibility: public -/
@[global_simps, irreducible]
def compact.LOGICAL_SEMANTIC : Result Std.Usize := verifier.SEMANTIC_BYTES

/-- [aspis_r1_cost_probe::compact::COMPACT_SEMANTIC]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 34:0-34:84
    Visibility: public -/
@[global_simps, irreducible]
def compact.COMPACT_SEMANTIC : Result Std.Usize := do
  let i ← compact.SEMANTIC_COMPACT_VALUES
  let i1 ← 16#usize * i
  let i2 ← compact.LOGICAL_SEMANTIC
  i2 - i1

/-- [aspis_r1_cost_probe::compact::OFF_Y1]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 39:0-39:58
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_Y1 : Result Std.Usize := do
  let i ← compact.COMPACT_SEMANTIC
  compact.OFF_SEMANTIC + i

/-- [aspis_r1_cost_probe::compact::COMPACT_Y1]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 35:0-35:38
    Visibility: public -/
@[global_simps, irreducible]
def compact.COMPACT_Y1 : Result Std.Usize := 29#usize * 16#usize

/-- [aspis_r1_cost_probe::compact::OFF_INACTIVE]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 40:0-40:52
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_INACTIVE : Result Std.Usize := do
  let i ← compact.OFF_Y1
  let i1 ← compact.COMPACT_Y1
  i + i1

/-- [aspis_r1_cost_probe::compact::OFF_ROUND0]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 41:0-41:48
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_ROUND0 : Result Std.Usize := do
  let i ← compact.OFF_INACTIVE
  i + 32#usize

/-- [aspis_r1_cost_probe::compact::OFF_FOLDED_ROOT]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 42:0-42:52
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_FOLDED_ROOT : Result Std.Usize := do
  let i ← compact.OFF_ROUND0
  i + 224#usize

/-- [aspis_r1_cost_probe::compact::OFF_ROUND1]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 43:0-43:51
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_ROUND1 : Result Std.Usize := do
  let i ← compact.OFF_FOLDED_ROOT
  i + 32#usize

/-- [aspis_r1_cost_probe::compact::OFF_FINAL]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 44:0-44:46
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_FINAL : Result Std.Usize := do
  let i ← compact.OFF_ROUND1
  i + 224#usize

/-- [aspis_r1_cost_probe::compact::OFF_OPENINGS]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 46:0-46:59
    Visibility: public -/
@[global_simps, irreducible]
def compact.OFF_OPENINGS : Result Std.Usize := do
  let i ← compact.FINAL_LEN * 32#usize
  let i1 ← compact.OFF_FINAL
  i1 + i

/-- [aspis_r1_cost_probe::compact::OPENING]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 37:0-37:58
    Visibility: public -/
@[global_simps, irreducible]
def compact.OPENING : Result Std.Usize := do
  let i ← 480#usize + 128#usize
  let i1 ← i + 32#usize
  let i2 ← i1 + 32#usize
  let i3 ← i2 + 128#usize
  i3 + 32#usize

/-- [aspis_r1_cost_probe::verifier::candidate::opening]:
    Source: 'crates/aspis-r1-cost-probe/src/candidate.rs', lines 29:0-32:1 -/
def verifier.candidate.opening
  (proof : Slice Std.U8) (i : Std.Usize) : Result (Slice Std.U8) := do
  let i1 ← compact.OPENING
  let i2 ← lift (Std.Usize.wrapping_mul i i1)
  let i3 ← compact.OFF_OPENINGS
  let at1 ← lift (Std.Usize.wrapping_add i3 i2)
  let i4 ← lift (Std.Usize.wrapping_add at1 i1)
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
    Std.U8) proof { start := at1, «end» := i4 }

/-- [aspis_r1_cost_probe::verifier::accumulated_weight_at]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 274:0-274:70 -/
def verifier.accumulated_weight_at
  (weights : Slice aspis_core.field.QM31) (index : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  Slice.index_usize weights index

/-- [aspis_r1_cost_probe::verifier::basis_at]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 272:0-272:61 -/
def verifier.basis_at
  (basis : Array aspis_core.field.M31 256#usize) (index : Std.Usize) :
  Result aspis_core.field.M31
  := do
  Array.index_usize basis index

/-- [aspis_r1_cost_probe::verifier::power_limb_at]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 233:0-233:64 -/
def verifier.power_limb_at
  (limbs : Array Std.U32 4#usize) (index : Std.Usize) : Result Std.U32 := do
  Array.index_usize limbs index

/-- [aspis_r1_cost_probe::verifier::residue_limb_at]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 231:0-231:62 -/
def verifier.residue_limb_at
  (row : Array Std.U64 4#usize) (index : Std.Usize) : Result Std.U64 := do
  Array.index_usize row index

/-- [aspis_r1_cost_probe::verifier::update_residue_row]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 237:4-241:5 -/
def verifier.update_residue_row_loop0.body
  (limbs : Array Std.U32 4#usize) (iter : core.ops.range.Range Std.Usize)
  (row : Array Std.U64 4#usize) (basis : aspis_core.field.M31) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    4#usize) × aspis_core.field.M31) (Array Std.U64 4#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done row)
  | some j =>
    let old ← verifier.residue_limb_at row j
    let limb ← verifier.power_limb_at limbs j
    let i ← lift (core.convert.num.FromU64U32.from limb)
    let i1 ← lift (core.convert.num.FromU64U32.from basis)
    let i2 ← lift (Std.U64.wrapping_mul i i1)
    let i3 ← lift (Std.U64.wrapping_add old i2)
    let row1 ← Array.update row j i3
    ok (cont (iter1, row1, basis))

/-- [aspis_r1_cost_probe::verifier::update_residue_row]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 237:4-241:5 -/
def verifier.update_residue_row_loop0
  (iter : core.ops.range.Range Std.Usize) (row : Array Std.U64 4#usize)
  (basis : aspis_core.field.M31) (limbs : Array Std.U32 4#usize) :
  Result (Array Std.U64 4#usize)
  := do
  loop
    (fun (iter1, row1, basis1) => verifier.update_residue_row_loop0.body limbs
      iter1 row1 basis1)
    (iter, row, basis)

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::verifier::update_residue_row]: loop body 1:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 243:8-243:64 -/
def verifier.update_residue_row_loop1.body
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  :
  Result (ControlFlow ((core.slice.iter.IterMut Std.U64) ×
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64))
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (fun im => let im1 := next_back im none
                                back im1))
  | some limb =>
    let i ← lift (limb &&& 2147483647#u64)
    let i1 ← lift (Std.U64.wrapping_shr limb 31#i32)
    let limb1 ← lift (Std.U64.wrapping_add i i1)
    ok (cont (iter1, fun im => let im1 := next_back im (some limb1)
                               back im1))
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::verifier::update_residue_row]: loop 1:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 243:8-243:64 -/
def verifier.update_residue_row_loop1
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  :
  Result (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  := do
  loop
    (fun (iter1, back1) => verifier.update_residue_row_loop1.body iter1 back1)
    (iter, back)
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::verifier::update_residue_row]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 235:0-245:1 -/
def verifier.update_residue_row
  (row : Array Std.U64 4#usize) (power : aspis_core.field.QM31)
  (basis : aspis_core.field.M31) (flush : Bool) :
  Result (Array Std.U64 4#usize)
  := do
  let i := power.c0.a
  let i1 := power.c0.b
  let i2 := power.c1.a
  let i3 := power.c1.b
  let row1 ←
    verifier.update_residue_row_loop0 { start := 0#usize, «end» := 4#usize }
      row basis (Array.make 4#usize [ i, i1, i2, i3 ])
  if flush
  then
    let (iter, into_iter_back) ←
      MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
        row1
    let back ← verifier.update_residue_row_loop1 iter (fun im => im)
    ok (into_iter_back back)
  else ok row1
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::BatchedWeights}::push]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 217:4-220:5 -/
def verifier.BatchedWeights.push
  (self : verifier.BatchedWeights) (index : Std.Usize)
  (power : aspis_core.field.QM31) (basis : aspis_core.field.M31) :
  Result verifier.BatchedWeights
  := do
  let i ← lift (self.terms &&& 3#usize)
  let (a, index_mut_back) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Array
      Std.U64 4#usize)) self.«raw» index
  let a1 ← verifier.update_residue_row a power basis (i = 3#usize)
  let v := index_mut_back a1
  ok { self with «raw» := v }
-/

/-- [aspis_r1_cost_probe::trace::value]:
    Source: 'crates/aspis-r1-cost-probe/src/trace.rs', lines 6:0-11:1
    Visibility: public -/
def trace.value
  (tag : Std.U16) (index : Std.Usize)
  (x : aspis_core.field.wide_exact.WideExact) :
  Result Unit
  := do
  ok ()

/-- [aspis_r1_cost_probe::verifier::accumulate_batched_with_node]: loop body 1:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 280:19-280:65 -/
def verifier.accumulate_batched_with_node_loop0_loop0.body
  (node : aspis_core.field.M31) (n : Std.Usize)
  (iter : core.ops.range.Range Std.Usize)
  (basis : Array aspis_core.field.M31 256#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array
    aspis_core.field.M31 256#usize)) (Array aspis_core.field.M31 256#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done basis)
  | some j =>
    let m ← Array.index_usize basis j
    let m1 ← aspis_core.field.M31.mul m node
    let i ← lift (Std.Usize.wrapping_add n j)
    let basis1 ← Array.update basis i m1
    ok (cont (iter1, basis1))

/-- [aspis_r1_cost_probe::verifier::accumulate_batched_with_node]: loop 1:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 280:19-280:65 -/
def verifier.accumulate_batched_with_node_loop0_loop0
  (iter : core.ops.range.Range Std.Usize) (node : aspis_core.field.M31)
  (basis : Array aspis_core.field.M31 256#usize) (n : Std.Usize) :
  Result (Array aspis_core.field.M31 256#usize)
  := do
  loop
    (fun (iter1, basis1) =>
      verifier.accumulate_batched_with_node_loop0_loop0.body node n iter1
      basis1)
    (iter, basis)

/-- [aspis_r1_cost_probe::verifier::accumulate_batched_with_node]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 280:4-280:115 -/
def verifier.accumulate_batched_with_node_loop0.body
  (m : aspis_core.field.M31) (width : Std.Usize) (node : aspis_core.field.M31)
  (basis : Array aspis_core.field.M31 256#usize) (n : Std.Usize) :
  Result (ControlFlow (aspis_core.field.M31 × (Array aspis_core.field.M31
    256#usize) × Std.Usize) (Array aspis_core.field.M31 256#usize))
  := do
  if n < width
  then
    let basis1 ←
      verifier.accumulate_batched_with_node_loop0_loop0
        { start := 0#usize, «end» := n } node basis n
    let m1 ← aspis_core.field.M31.mul node node
    let m2 ← aspis_core.field.M31.double m1
    let node1 ← aspis_core.field.M31.sub m2 m
    let n1 ← lift (Std.Usize.wrapping_mul n 2#usize)
    ok (cont (node1, basis1, n1))
  else ok (done basis)

/-- [aspis_r1_cost_probe::verifier::accumulate_batched_with_node]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 280:4-280:115 -/
def verifier.accumulate_batched_with_node_loop0
  (m : aspis_core.field.M31) (node : aspis_core.field.M31) (width : Std.Usize)
  (basis : Array aspis_core.field.M31 256#usize) (n : Std.Usize) :
  Result (Array aspis_core.field.M31 256#usize)
  := do
  loop
    (fun (node1, basis1, n1) =>
      verifier.accumulate_batched_with_node_loop0.body m width node1 basis1 n1)
    (node, basis, n)

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::verifier::accumulate_batched_with_node]: loop body 2:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 281:4-286:5 -/
def verifier.accumulate_batched_with_node_loop1.body
  (v : alloc.vec.Vec aspis_core.field.QM31) (q : aspis_core.field.QM31)
  (i : Std.Usize) (width : Std.Usize)
  (basis : Array aspis_core.field.M31 256#usize)
  (iter : core.ops.range.Range Std.Usize) (weights : verifier.BatchedWeights) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) ×
    verifier.BatchedWeights) verifier.BatchedWeights)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done weights)
  | some j =>
    let m ← verifier.basis_at basis j
    let weights1 ← verifier.BatchedWeights.push weights j q m
    let i1 ← lift (Std.Usize.wrapping_mul i width)
    let i2 ← lift (Std.Usize.wrapping_add i1 j)
    let s := alloc.vec.Vec.deref v
    let q1 ← verifier.accumulated_weight_at s j
    let we ← aspis_core.field.wide_exact.WideExact.from_qm31 q1
    trace.value 12#u16 i2 we
    let i3 ← lift (Std.Usize.wrapping_mul i width)
    let i4 ← lift (Std.Usize.wrapping_add i3 j)
    let we1 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        m
    trace.value 13#u16 i4 we1
    ok (cont (iter1, weights1))
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::verifier::accumulate_batched_with_node]: loop 2:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 281:4-286:5 -/
def verifier.accumulate_batched_with_node_loop1
  (iter : core.ops.range.Range Std.Usize)
  (v : alloc.vec.Vec aspis_core.field.QM31) (q : aspis_core.field.QM31)
  (i : Std.Usize) (weights : verifier.BatchedWeights) (width : Std.Usize)
  (basis : Array aspis_core.field.M31 256#usize) :
  Result verifier.BatchedWeights
  := do
  loop
    (fun (iter1, weights1) => verifier.accumulate_batched_with_node_loop1.body
      v q i width basis iter1 weights1)
    (iter, weights)
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::verifier::accumulate_batched_with_node]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 277:0-290:1 -/
def verifier.accumulate_batched_with_node
  (p : verifier.Prepared) (a : verifier.Accumulator)
  (node : aspis_core.field.M31) (value : aspis_core.field.wide_exact.WideExact)
  (weights : verifier.BatchedWeights) :
  Result (verifier.Accumulator × verifier.BatchedWeights)
  := do
  let width := alloc.vec.Vec.len a.weights
  let m ← aspis_core.field.M31.ZERO
  let basis := Array.repeat 256#usize m
  let m1 ← aspis_core.field.M31.ONE
  let basis1 ← Array.update basis 0#usize m1
  let basis2 ←
    verifier.accumulate_batched_with_node_loop0 m1 node width basis1 1#usize
  let weights1 ←
    verifier.accumulate_batched_with_node_loop1
      { start := 0#usize, «end» := width } a.weights a.power a.next weights
      width basis2
  let i ← lift (Std.Usize.wrapping_add weights1.terms 1#usize)
  let we ← aspis_core.field.wide_exact.WideExact.mul_qm31 value a.power
  let we1 ← aspis_core.field.wide_exact.WideExact.add a.rhs we
  trace.value 11#u16 a.next we1
  let q ← aspis_core.field.QM31.mul a.power p.rho
  let i1 ← lift (Std.Usize.wrapping_add a.next 1#usize)
  ok ({ a with rhs := we1, power := q, next := i1 },
    { weights1 with terms := i })
-/

/-- [aspis_r1_cost_probe::weights::QUARTER]
    Source: 'crates/aspis-r1-cost-probe/src/weights.rs', lines 5:0-5:37
    Visibility: public -/
@[global_simps, irreducible]
def weights.QUARTER : aspis_core.field.M31 := 536870912#u32

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::verifier::line_fold_with_inverses]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 191:0-200:1 -/
def verifier.line_fold_with_inverses
  (alpha : aspis_core.field.wide_exact.WideExact)
  (a : Array aspis_core.field.wide_exact.WideExact 4#usize)
  (inverse : Array aspis_core.field.M31 5#usize) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  let ix ← Array.index_usize inverse 2#usize
  let iy ← Array.index_usize inverse 3#usize
  let iz ← Array.index_usize inverse 4#usize
  let a1 ← Array.index_usize a 0#usize
  let b ← Array.index_usize a 1#usize
  let c ← Array.index_usize a 2#usize
  let d ← Array.index_usize a 3#usize
  let we ← aspis_core.field.wide_exact.WideExact.add a1 b
  let we1 ← aspis_core.field.wide_exact.WideExact.add we c
  let we2 ← aspis_core.field.wide_exact.WideExact.add we1 d
  let h0 ← aspis_core.field.wide_exact.WideExact.mul_m31 we2 weights.QUARTER
  let we3 ← aspis_core.field.wide_exact.WideExact.sub we c
  let we4 ← aspis_core.field.wide_exact.WideExact.sub we3 d
  let m ← aspis_core.field.M31.mul weights.QUARTER iz
  let h2 ← aspis_core.field.wide_exact.WideExact.mul_m31 we4 m
  let we5 ← aspis_core.field.wide_exact.WideExact.sub a1 b
  let m1 ← aspis_core.field.M31.mul 1073741824#u32 ix
  let c0 ← aspis_core.field.wide_exact.WideExact.mul_m31 we5 m1
  let we6 ← aspis_core.field.wide_exact.WideExact.sub d c
  let m2 ← aspis_core.field.M31.mul 1073741824#u32 iy
  let c1 ← aspis_core.field.wide_exact.WideExact.mul_m31 we6 m2
  let we7 ← aspis_core.field.wide_exact.WideExact.add c0 c1
  let h1 ← aspis_core.field.wide_exact.WideExact.mul_m31 we7 1073741824#u32
  let we8 ← aspis_core.field.wide_exact.WideExact.sub c0 c1
  let m3 ← aspis_core.field.M31.mul 1073741824#u32 iz
  let h3 ← aspis_core.field.wide_exact.WideExact.mul_m31 we8 m3
  let we9 ← aspis_core.field.wide_exact.WideExact.mul alpha h3
  let we10 ← aspis_core.field.wide_exact.WideExact.add h2 we9
  let we11 ← aspis_core.field.wide_exact.WideExact.mul alpha we10
  let we12 ← aspis_core.field.wide_exact.WideExact.add h1 we11
  let we13 ← aspis_core.field.wide_exact.WideExact.mul alpha we12
  aspis_core.field.wide_exact.WideExact.add h0 we13
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::verifier::circle_fold_with_inverses]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 182:0-189:1 -/
def verifier.circle_fold_with_inverses
  (alpha : aspis_core.field.wide_exact.WideExact)
  (a : Array aspis_core.field.wide_exact.WideExact 4#usize)
  (inverse : Array aspis_core.field.M31 5#usize) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  let ix ← Array.index_usize inverse 0#usize
  let iy ← Array.index_usize inverse 1#usize
  let a1 ← Array.index_usize a 0#usize
  let b ← Array.index_usize a 1#usize
  let c ← Array.index_usize a 2#usize
  let d ← Array.index_usize a 3#usize
  let we ← aspis_core.field.wide_exact.WideExact.add a1 b
  let we1 ← aspis_core.field.wide_exact.WideExact.add we c
  let we2 ← aspis_core.field.wide_exact.WideExact.add we1 d
  let h0 ← aspis_core.field.wide_exact.WideExact.mul_m31 we2 weights.QUARTER
  let we3 ← aspis_core.field.wide_exact.WideExact.sub a1 b
  let we4 ← aspis_core.field.wide_exact.WideExact.sub we3 c
  let we5 ← aspis_core.field.wide_exact.WideExact.add we4 d
  let m ← aspis_core.field.M31.mul weights.QUARTER iy
  let h1 ← aspis_core.field.wide_exact.WideExact.mul_m31 we5 m
  let we6 ← aspis_core.field.wide_exact.WideExact.sub we c
  let we7 ← aspis_core.field.wide_exact.WideExact.sub we6 d
  let m1 ← aspis_core.field.M31.mul weights.QUARTER ix
  let h2 ← aspis_core.field.wide_exact.WideExact.mul_m31 we7 m1
  let we8 ← aspis_core.field.wide_exact.WideExact.add we3 c
  let we9 ← aspis_core.field.wide_exact.WideExact.sub we8 d
  let m2 ← aspis_core.field.M31.mul m1 iy
  let h3 ← aspis_core.field.wide_exact.WideExact.mul_m31 we9 m2
  let we10 ← aspis_core.field.wide_exact.WideExact.mul alpha h3
  let we11 ← aspis_core.field.wide_exact.WideExact.add h2 we10
  let we12 ← aspis_core.field.wide_exact.WideExact.mul alpha we11
  let we13 ← aspis_core.field.wide_exact.WideExact.add h1 we12
  let we14 ← aspis_core.field.wide_exact.WideExact.mul alpha we13
  aspis_core.field.wide_exact.WideExact.add h0 we14
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_query]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 179:4-179:80 -/
def verifier.QueryGeometry.for_query
  (self : verifier.QueryGeometry) (index : Std.Usize) :
  Result (Array aspis_core.field.M31 5#usize)
  := do
  let i ← lift (Std.Usize.wrapping_sub index self.start)
  alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array
    aspis_core.field.M31 5#usize)) self.inverses i
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::verifier::mark]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 31:0-31:60 -/
def verifier.mark
  (obs : Option (verifier.Phase → Result Unit)) (p : verifier.Phase) :
  Result Unit
  := do
  match obs with
  | none => ok ()
  | some f => f p
-/

/-- [aspis_r1_cost_probe::fast_pairing::canonical::P]
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 5:4-5:32
    Visibility: public -/
@[global_simps, irreducible]
def fast_pairing.canonical.P : Std.U32 := 2147483647#u32

/-- [aspis_r1_cost_probe::fast_pairing::canonical::reduce]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 10:22-14:5 -/
def fast_pairing.canonical.reduce (x : Std.U64) : Result Std.U32 := do
  let i ← lift (core.convert.num.FromU64U32.from fast_pairing.canonical.P)
  let i1 ← lift (x &&& i)
  let i2 ← lift (Std.U64.wrapping_shr x 31#u32)
  let x1 ← lift (Std.U64.wrapping_add i1 i2)
  let i3 ← lift (core.convert.num.FromU64U32.from fast_pairing.canonical.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← lift (Std.U64.wrapping_shr x1 31#u32)
  let x2 ← lift (Std.U64.wrapping_add i4 i5)
  let i6 ← lift (core.convert.num.FromU64U32.from fast_pairing.canonical.P)
  if x2 >= i6
  then
    let i7 ← lift (core.convert.num.FromU64U32.from fast_pairing.canonical.P)
    let i8 ← lift (Std.U64.wrapping_sub x2 i7)
    ok (UScalar.cast .U32 i8)
  else ok (UScalar.cast .U32 x2)

/-- [aspis_r1_cost_probe::fast_pairing::canonical::{aspis_r1_cost_probe::fast_pairing::canonical::Dot}::finish]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 123:8-123:121
    Visibility: public -/
def fast_pairing.canonical.Dot.finish
  (self : fast_pairing.canonical.Dot) : Result fast_pairing.canonical.Q := do
  let i ← Array.index_usize self.sums 0#usize
  let i1 ← fast_pairing.canonical.reduce i
  let i2 ← Array.index_usize self.sums 1#usize
  let i3 ← fast_pairing.canonical.reduce i2
  let i4 ← Array.index_usize self.sums 2#usize
  let i5 ← fast_pairing.canonical.reduce i4
  let i6 ← Array.index_usize self.sums 3#usize
  let i7 ← fast_pairing.canonical.reduce i6
  ok (Array.make 4#usize [ i1, i3, i5, i7 ])

/-- [aspis_r1_cost_probe::fast_pairing::canonical::{aspis_r1_cost_probe::fast_pairing::canonical::Q}::limbs]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 29:8-29:49
    Visibility: public -/
def fast_pairing.canonical.Q.limbs
  (self : fast_pairing.canonical.Q) : Result (Array Std.U32 4#usize) := do
  ok self

/-- [aspis_r1_cost_probe::fast_pairing::{aspis_r1_cost_probe::fast_pairing::EbyKDot}::finish]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 176:4-181:5
    Visibility: public -/
def fast_pairing.EbyKDot.finish
  (self : fast_pairing.EbyKDot) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  let q ← fast_pairing.canonical.Dot.finish self.c0
  let a ← fast_pairing.canonical.Q.limbs q
  let a1 ← Array.index_usize a 0#usize
  let b ← Array.index_usize a 1#usize
  let c ← Array.index_usize a 2#usize
  let d ← Array.index_usize a 3#usize
  let q1 ← fast_pairing.canonical.Dot.finish self.c1
  let a2 ← fast_pairing.canonical.Q.limbs q1
  let e ← Array.index_usize a2 0#usize
  let f ← Array.index_usize a2 1#usize
  let g ← Array.index_usize a2 2#usize
  let h ← Array.index_usize a2 3#usize
  let o ←
    aspis_core.field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [ a1, b, c, d, e, f, g, h ])
  core.option.Option.unwrap o

/-- [aspis_r1_cost_probe::fast_pairing::limbs_of]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 133:0-135:1 -/
def fast_pairing.limbs_of
  (k : aspis_core.field.QM31) : Result (Array Std.U32 4#usize) := do
  let i := k.c0.a
  let i1 := k.c0.b
  let i2 := k.c1.a
  let i3 := k.c1.b
  ok (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [aspis_r1_cost_probe::fast_pairing::canonical::{aspis_r1_cost_probe::fast_pairing::canonical::Q}::from_limbs]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 24:8-27:9
    Visibility: public -/
def fast_pairing.canonical.Q.from_limbs
  (x : Array Std.U32 4#usize) : Result (Option fast_pairing.canonical.Q) := do
  let a ← Array.index_usize x 0#usize
  let b ← Array.index_usize x 1#usize
  let c ← Array.index_usize x 2#usize
  let d ← Array.index_usize x 3#usize
  if a < fast_pairing.canonical.P
  then
    if b < fast_pairing.canonical.P
    then
      if c < fast_pairing.canonical.P
      then
        if d < fast_pairing.canonical.P
        then ok (some (Array.make 4#usize [ a, b, c, d ]))
        else ok none
      else ok none
    else ok none
  else ok none

/-- [aspis_r1_cost_probe::fast_pairing::checked_q]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 138:0-140:1 -/
def fast_pairing.checked_q
  (k : aspis_core.field.QM31) :
  Result (core.result.Result fast_pairing.canonical.Q Unit)
  := do
  let a ← fast_pairing.limbs_of k
  let o ← fast_pairing.canonical.Q.from_limbs a
  match o with
  | none => ok (core.result.Result.Err ())
  | some q => ok (core.result.Result.Ok q)

/-- [aspis_r1_cost_probe::fast_pairing::MAX_TERMS]
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 130:0-130:30 -/
@[global_simps, irreducible]
def fast_pairing.MAX_TERMS : Std.Usize := 4096#usize

/-- [aspis_r1_cost_probe::fast_pairing::canonical::{aspis_r1_cost_probe::fast_pairing::canonical::Q}::from_wide]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 33:8-36:9 -/
def fast_pairing.canonical.Q.from_wide
  (value : aspis_core.field.wide_exact.WideExact) :
  Result (Array fast_pairing.canonical.Q 2#usize)
  := do
  let a ← aspis_core.field.wide_exact.WideExact.to_limbs value
  let a1 ← Array.index_usize a 0#usize
  let b ← Array.index_usize a 1#usize
  let c ← Array.index_usize a 2#usize
  let d ← Array.index_usize a 3#usize
  let e ← Array.index_usize a 4#usize
  let f ← Array.index_usize a 5#usize
  let g ← Array.index_usize a 6#usize
  let h ← Array.index_usize a 7#usize
  ok
    (Array.make 2#usize [
      Array.make 4#usize [ a1, b, c, d ], Array.make 4#usize [ e, f, g, h ]
      ])

/-- [aspis_r1_cost_probe::fast_pairing::{aspis_r1_cost_probe::fast_pairing::EbyKDot}::push]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 165:4-173:5
    Visibility: public -/
def fast_pairing.EbyKDot.push
  (self : fast_pairing.EbyKDot) (value : aspis_core.field.wide_exact.WideExact)
  (scalar : aspis_core.field.QM31) :
  Result ((core.result.Result Unit Unit) × fast_pairing.EbyKDot)
  := do
  if self.count >= fast_pairing.MAX_TERMS
  then ok (core.result.Result.Err (), self)
  else
    let a ← fast_pairing.canonical.Q.from_wide value
    let value_c0 ← Array.index_usize a 0#usize
    let value_c1 ← Array.index_usize a 1#usize
    let r ← fast_pairing.checked_q scalar
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let d ← fast_pairing.canonical.Dot.push self.c0 value_c0 val
      let d1 ← fast_pairing.canonical.Dot.push self.c1 value_c1 val
      let i ← lift (Std.Usize.wrapping_add self.count 1#usize)
      ok (core.result.Result.Ok (), { c0 := d, c1 := d1, count := i })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame Unit) residual
      ok (r1, self)

/-- [aspis_r1_cost_probe::fast_pairing::canonical::{aspis_r1_cost_probe::fast_pairing::canonical::Dot}::new]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 112:8-112:45
    Visibility: public -/
def fast_pairing.canonical.Dot.new : Result fast_pairing.canonical.Dot := do
  let a := Array.repeat 4#usize 0#u64
  ok { sums := a }

/-- [aspis_r1_cost_probe::fast_pairing::{aspis_r1_cost_probe::fast_pairing::EbyKDot}::new]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 160:4-162:5
    Visibility: public -/
def fast_pairing.EbyKDot.new : Result fast_pairing.EbyKDot := do
  let d ← fast_pairing.canonical.Dot.new
  ok { c0 := d, c1 := d, count := 0#usize }

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::fast_dots::four_dots_one]: loop body 1:
    Source: 'crates/aspis-r1-cost-probe/src/fast_dots.rs', lines 19:12-35:13 -/
def fast_dots.four_dots_one_loop0_loop0.body
  (q : Array Std.U8 608#usize)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (slot : Std.Usize)
  (iter : core.ops.range.Range Std.Usize) (sums : Array Std.U64 8#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    8#usize)) (Array Std.U64 8#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sums)
  | some term =>
    let i ← lift (Std.Usize.wrapping_mul slot 120#usize)
    let i1 ← lift (Std.Usize.wrapping_mul term 4#usize)
    let i2 ← lift (Std.Usize.wrapping_add i i1)
    let i3 ← lift (Std.Usize.wrapping_mul slot 120#usize)
    let i4 ← lift (Std.Usize.wrapping_mul term 4#usize)
    let i5 ← lift (Std.Usize.wrapping_add i3 i4)
    let i6 ← lift (Std.Usize.wrapping_add i5 4#usize)
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q
        { start := i2, «end» := i6 }
    let r ←
      core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s
    let a ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
    let o1 ← aspis_core.field.M31.from_le_bytes a
    let scalar ← core.option.Option.unwrap o1
    let we ← Array.index_usize g term
    let coefficient ← aspis_core.field.wide_exact.WideExact.to_limbs we
    let i7 ← Array.index_usize coefficient 0#usize
    let i8 ← lift (core.convert.num.FromU64U32.from i7)
    let i9 ← lift (core.convert.num.FromU64U32.from scalar)
    let i10 ← lift (Std.U64.wrapping_mul i8 i9)
    let i11 ← Array.index_usize sums 0#usize
    let i12 ← lift (Std.U64.wrapping_add i11 i10)
    let sums1 ← Array.update sums 0#usize i12
    let i13 ← Array.index_usize coefficient 1#usize
    let i14 ← lift (core.convert.num.FromU64U32.from i13)
    let i15 ← lift (core.convert.num.FromU64U32.from scalar)
    let i16 ← lift (Std.U64.wrapping_mul i14 i15)
    let i17 ← Array.index_usize sums1 1#usize
    let i18 ← lift (Std.U64.wrapping_add i17 i16)
    let sums2 ← Array.update sums1 1#usize i18
    let i19 ← Array.index_usize coefficient 2#usize
    let i20 ← lift (core.convert.num.FromU64U32.from i19)
    let i21 ← lift (core.convert.num.FromU64U32.from scalar)
    let i22 ← lift (Std.U64.wrapping_mul i20 i21)
    let i23 ← Array.index_usize sums2 2#usize
    let i24 ← lift (Std.U64.wrapping_add i23 i22)
    let sums3 ← Array.update sums2 2#usize i24
    let i25 ← Array.index_usize coefficient 3#usize
    let i26 ← lift (core.convert.num.FromU64U32.from i25)
    let i27 ← lift (core.convert.num.FromU64U32.from scalar)
    let i28 ← lift (Std.U64.wrapping_mul i26 i27)
    let i29 ← Array.index_usize sums3 3#usize
    let i30 ← lift (Std.U64.wrapping_add i29 i28)
    let sums4 ← Array.update sums3 3#usize i30
    let i31 ← Array.index_usize coefficient 4#usize
    let i32 ← lift (core.convert.num.FromU64U32.from i31)
    let i33 ← lift (core.convert.num.FromU64U32.from scalar)
    let i34 ← lift (Std.U64.wrapping_mul i32 i33)
    let i35 ← Array.index_usize sums4 4#usize
    let i36 ← lift (Std.U64.wrapping_add i35 i34)
    let sums5 ← Array.update sums4 4#usize i36
    let i37 ← Array.index_usize coefficient 5#usize
    let i38 ← lift (core.convert.num.FromU64U32.from i37)
    let i39 ← lift (core.convert.num.FromU64U32.from scalar)
    let i40 ← lift (Std.U64.wrapping_mul i38 i39)
    let i41 ← Array.index_usize sums5 5#usize
    let i42 ← lift (Std.U64.wrapping_add i41 i40)
    let sums6 ← Array.update sums5 5#usize i42
    let i43 ← Array.index_usize coefficient 6#usize
    let i44 ← lift (core.convert.num.FromU64U32.from i43)
    let i45 ← lift (core.convert.num.FromU64U32.from scalar)
    let i46 ← lift (Std.U64.wrapping_mul i44 i45)
    let i47 ← Array.index_usize sums6 6#usize
    let i48 ← lift (Std.U64.wrapping_add i47 i46)
    let sums7 ← Array.update sums6 6#usize i48
    let i49 ← Array.index_usize coefficient 7#usize
    let i50 ← lift (core.convert.num.FromU64U32.from i49)
    let i51 ← lift (core.convert.num.FromU64U32.from scalar)
    let i52 ← lift (Std.U64.wrapping_mul i50 i51)
    let i53 ← Array.index_usize sums7 7#usize
    let i54 ← lift (Std.U64.wrapping_add i53 i52)
    let sums8 ← Array.update sums7 7#usize i54
    ok (cont (iter1, sums8))
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::fast_dots::four_dots_one]: loop 1:
    Source: 'crates/aspis-r1-cost-probe/src/fast_dots.rs', lines 19:12-35:13 -/
def fast_dots.four_dots_one_loop0_loop0
  (iter : core.ops.range.Range Std.Usize) (q : Array Std.U8 608#usize)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (slot : Std.Usize)
  (sums : Array Std.U64 8#usize) :
  Result (Array Std.U64 8#usize)
  := do
  loop
    (fun (iter1, sums1) => fast_dots.four_dots_one_loop0_loop0.body q g slot
      iter1 sums1)
    (iter, sums)
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::fast_dots::four_dots_one]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/fast_dots.rs', lines 17:8-44:9 -/
def fast_dots.four_dots_one_loop0.body
  (q : Array Std.U8 608#usize)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (slot : Std.Usize)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (limbs : Array Std.U64 8#usize) :
  Result (ControlFlow ((core.iter.adapters.step_by.StepBy (core.ops.range.Range
    Std.Usize)) × (Array Std.U64 8#usize)) (Array Std.U64 8#usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (done limbs)
  | some start =>
    let sums := Array.repeat 8#usize 0#u64
    let i ← lift (Std.Usize.wrapping_add start 4#usize)
    let i1 ← core.cmp.min core.cmp.OrdUsize i 26#usize
    let sums1 ←
      fast_dots.four_dots_one_loop0_loop0 { start, «end» := i1 } q g slot
        sums
    let i2 ← Array.index_usize sums1 0#usize
    let i3 ← lift (i2 &&& 2147483647#u64)
    let i4 ← lift (Std.U64.wrapping_shr i2 31#i32)
    let i5 ← lift (Std.U64.wrapping_add i3 i4)
    let i6 ← Array.index_usize limbs 0#usize
    let i7 ← lift (Std.U64.wrapping_add i6 i5)
    let limbs1 ← Array.update limbs 0#usize i7
    let i8 ← Array.index_usize sums1 1#usize
    let i9 ← lift (i8 &&& 2147483647#u64)
    let i10 ← lift (Std.U64.wrapping_shr i8 31#i32)
    let i11 ← lift (Std.U64.wrapping_add i9 i10)
    let i12 ← Array.index_usize limbs1 1#usize
    let i13 ← lift (Std.U64.wrapping_add i12 i11)
    let limbs2 ← Array.update limbs1 1#usize i13
    let i14 ← Array.index_usize sums1 2#usize
    let i15 ← lift (i14 &&& 2147483647#u64)
    let i16 ← lift (Std.U64.wrapping_shr i14 31#i32)
    let i17 ← lift (Std.U64.wrapping_add i15 i16)
    let i18 ← Array.index_usize limbs2 2#usize
    let i19 ← lift (Std.U64.wrapping_add i18 i17)
    let limbs3 ← Array.update limbs2 2#usize i19
    let i20 ← Array.index_usize sums1 3#usize
    let i21 ← lift (i20 &&& 2147483647#u64)
    let i22 ← lift (Std.U64.wrapping_shr i20 31#i32)
    let i23 ← lift (Std.U64.wrapping_add i21 i22)
    let i24 ← Array.index_usize limbs3 3#usize
    let i25 ← lift (Std.U64.wrapping_add i24 i23)
    let limbs4 ← Array.update limbs3 3#usize i25
    let i26 ← Array.index_usize sums1 4#usize
    let i27 ← lift (i26 &&& 2147483647#u64)
    let i28 ← lift (Std.U64.wrapping_shr i26 31#i32)
    let i29 ← lift (Std.U64.wrapping_add i27 i28)
    let i30 ← Array.index_usize limbs4 4#usize
    let i31 ← lift (Std.U64.wrapping_add i30 i29)
    let limbs5 ← Array.update limbs4 4#usize i31
    let i32 ← Array.index_usize sums1 5#usize
    let i33 ← lift (i32 &&& 2147483647#u64)
    let i34 ← lift (Std.U64.wrapping_shr i32 31#i32)
    let i35 ← lift (Std.U64.wrapping_add i33 i34)
    let i36 ← Array.index_usize limbs5 5#usize
    let i37 ← lift (Std.U64.wrapping_add i36 i35)
    let limbs6 ← Array.update limbs5 5#usize i37
    let i38 ← Array.index_usize sums1 6#usize
    let i39 ← lift (i38 &&& 2147483647#u64)
    let i40 ← lift (Std.U64.wrapping_shr i38 31#i32)
    let i41 ← lift (Std.U64.wrapping_add i39 i40)
    let i42 ← Array.index_usize limbs6 6#usize
    let i43 ← lift (Std.U64.wrapping_add i42 i41)
    let limbs7 ← Array.update limbs6 6#usize i43
    let i44 ← Array.index_usize sums1 7#usize
    let i45 ← lift (i44 &&& 2147483647#u64)
    let i46 ← lift (Std.U64.wrapping_shr i44 31#i32)
    let i47 ← lift (Std.U64.wrapping_add i45 i46)
    let i48 ← Array.index_usize limbs7 7#usize
    let i49 ← lift (Std.U64.wrapping_add i48 i47)
    let limbs8 ← Array.update limbs7 7#usize i49
    ok (cont (iter1, limbs8))
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::fast_dots::four_dots_one]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/fast_dots.rs', lines 17:8-44:9 -/
def fast_dots.four_dots_one_loop0
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (q : Array Std.U8 608#usize)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (slot : Std.Usize)
  (limbs : Array Std.U64 8#usize) :
  Result (Array Std.U64 8#usize)
  := do
  loop
    (fun (iter1, limbs1) => fast_dots.four_dots_one_loop0.body q g slot iter1
      limbs1)
    (iter, limbs)
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::fast_dots::four_dots_one]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_dots.rs', lines 15:0-64:1 -/
def fast_dots.four_dots_one
  (q : Array Std.U8 608#usize)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (slot : Std.Usize)
  :
  Result aspis_core.field.wide_exact.WideExact
  := do
  let limbs := Array.repeat 8#usize 0#u64
  let iter ←
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := 26#usize } 4#usize
  let limbs1 ← fast_dots.four_dots_one_loop0 iter q g slot limbs
  let i ← Array.index_usize limbs1 0#usize
  let m ← aspis_core.field.M31.reduce_u64 i
  let i1 ← Array.index_usize limbs1 1#usize
  let m1 ← aspis_core.field.M31.reduce_u64 i1
  let i2 ← Array.index_usize limbs1 2#usize
  let m2 ← aspis_core.field.M31.reduce_u64 i2
  let i3 ← Array.index_usize limbs1 3#usize
  let m3 ← aspis_core.field.M31.reduce_u64 i3
  let i4 ← Array.index_usize limbs1 4#usize
  let m4 ← aspis_core.field.M31.reduce_u64 i4
  let i5 ← Array.index_usize limbs1 5#usize
  let m5 ← aspis_core.field.M31.reduce_u64 i5
  let i6 ← Array.index_usize limbs1 6#usize
  let m6 ← aspis_core.field.M31.reduce_u64 i6
  let i7 ← Array.index_usize limbs1 7#usize
  let m7 ← aspis_core.field.M31.reduce_u64 i7
  let o ←
    aspis_core.field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [ m, m1, m2, m3, m4, m5, m6, m7 ])
  let value ← core.option.Option.unwrap o
  let tail ← fast_pairing.EbyKDot.new
  let we ← Array.index_usize g 28#usize
  let i8 ← lift (Std.Usize.wrapping_mul slot 120#usize)
  let i9 ← lift (Std.Usize.wrapping_add i8 104#usize)
  let i10 ← lift (Std.Usize.wrapping_mul slot 120#usize)
  let i11 ← lift (Std.Usize.wrapping_add i10 120#usize)
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q
      { start := i9, «end» := i11 }
  let o1 ← aspis_core.field.QM31.from_le_bytes s
  let q1 ← core.option.Option.unwrap o1
  let (r, tail1) ← fast_pairing.EbyKDot.push tail we q1
  core.result.Result.unwrap core.fmt.DebugUnit r
  let i12 ← lift (Std.Usize.wrapping_mul slot 32#usize)
  let i13 ← lift (Std.Usize.wrapping_add 480#usize i12)
  let i14 ← lift (Std.Usize.wrapping_mul 0#usize 16#usize)
  let offset0 ← lift (Std.Usize.wrapping_add i13 i14)
  let i15 ← lift (Std.Usize.wrapping_add 0#usize 26#usize)
  let we1 ← Array.index_usize g i15
  let i16 ← lift (Std.Usize.wrapping_add offset0 16#usize)
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q
      { start := offset0, «end» := i16 }
  let o2 ← aspis_core.field.QM31.from_le_bytes s1
  let q2 ← core.option.Option.unwrap o2
  let (r1, tail2) ← fast_pairing.EbyKDot.push tail1 we1 q2
  core.result.Result.unwrap core.fmt.DebugUnit r1
  let i17 ← lift (Std.Usize.wrapping_mul slot 32#usize)
  let i18 ← lift (Std.Usize.wrapping_add 480#usize i17)
  let i19 ← lift (Std.Usize.wrapping_mul 1#usize 16#usize)
  let offset1 ← lift (Std.Usize.wrapping_add i18 i19)
  let i20 ← lift (Std.Usize.wrapping_add 1#usize 26#usize)
  let we2 ← Array.index_usize g i20
  let i21 ← lift (Std.Usize.wrapping_add offset1 16#usize)
  let s2 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q
      { start := offset1, «end» := i21 }
  let o3 ← aspis_core.field.QM31.from_le_bytes s2
  let q3 ← core.option.Option.unwrap o3
  let (r2, tail3) ← fast_pairing.EbyKDot.push tail2 we2 q3
  core.result.Result.unwrap core.fmt.DebugUnit r2
  let we3 ← fast_pairing.EbyKDot.finish tail3
  aspis_core.field.wide_exact.WideExact.add value we3
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::fast_dots::four_dots]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_dots.rs', lines 67:0-75:1
    Visibility: public -/
def fast_dots.four_dots
  (q : Slice Std.U8) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
  :
  Result (Array aspis_core.field.wide_exact.WideExact 4#usize)
  := do
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice
      Std.U8) q { «end» := 608#usize }
  let r ← core.array.TryFromSharedArraySlice.try_from 608#usize s
  let q1 ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  let we ← fast_dots.four_dots_one q1 g 0#usize
  let we1 ← fast_dots.four_dots_one q1 g 1#usize
  let we2 ← fast_dots.four_dots_one q1 g 2#usize
  let we3 ← fast_dots.four_dots_one q1 g 3#usize
  ok (Array.make 4#usize [ we, we1, we2, we3 ])
-/

/-- [aspis_r1_cost_probe::weights::field]:
    Source: 'crates/aspis-r1-cost-probe/src/weights.rs', lines 25:0-25:90
    Visibility: public -/
def weights.field
  (bytes : Slice Std.U8) (i : Std.Usize) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  let i1 ← lift (Std.Usize.wrapping_mul i 32#usize)
  let i2 ← lift (Std.Usize.wrapping_add i 1#usize)
  let i3 ← lift (Std.Usize.wrapping_mul i2 32#usize)
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) bytes { start := i1, «end» := i3 }
  let o ← aspis_core.field.wide_exact.WideExact.from_le_bytes s
  core.option.Option.unwrap o

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::verifier::candidate::query_values::{impl core::ops::function::FnMut<(usize,), aspis_core::field::wide_exact::WideExact> for aspis_r1_cost_probe::verifier::candidate::query_values::closure<'_0>}::call_mut]:
    Source: 'crates/aspis-r1-cost-probe/src/candidate.rs', lines 224:38-224:64 -/
def
  verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
  (c : verifier.candidate.query_values.closure) (tupled_args : Std.Usize) :
  Result (aspis_core.field.wide_exact.WideExact ×
    verifier.candidate.query_values.closure)
  := do
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) c { start := 672#usize, «end» := 800#usize }
  let we ← weights.field s tupled_args
  ok (we, c)
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::verifier::candidate::query_values::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::wide_exact::WideExact> for aspis_r1_cost_probe::verifier::candidate::query_values::closure<'_0>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/candidate.rs', lines 224:38-224:64 -/
def
  verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
  (c : verifier.candidate.query_values.closure) (i : Std.Usize) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  let (we, _) ←
    verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      c i
  ok we
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- Trait implementation: [aspis_r1_cost_probe::verifier::candidate::query_values::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::wide_exact::WideExact> for aspis_r1_cost_probe::verifier::candidate::query_values::closure<'_0>}]
    Source: 'crates/aspis-r1-cost-probe/src/candidate.rs', lines 224:38-224:64 -/
@[reducible]
def
  verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact
  : core.ops.function.FnOnce verifier.candidate.query_values.closure Std.Usize
  aspis_core.field.wide_exact.WideExact := {
  call_once :=
    verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
}
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- Trait implementation: [aspis_r1_cost_probe::verifier::candidate::query_values::{impl core::ops::function::FnMut<(usize,), aspis_core::field::wide_exact::WideExact> for aspis_r1_cost_probe::verifier::candidate::query_values::closure<'_0>}]
    Source: 'crates/aspis-r1-cost-probe/src/candidate.rs', lines 224:38-224:64 -/
@[reducible]
def
  verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
  : core.ops.function.FnMut verifier.candidate.query_values.closure Std.Usize
  aspis_core.field.wide_exact.WideExact := {
  FnOnceInst :=
    verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact
  call_mut :=
    verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
}
-/

/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):
/-- [aspis_r1_cost_probe::verifier::candidate::query_values]:
    Source: 'crates/aspis-r1-cost-probe/src/candidate.rs', lines 212:0-235:1 -/
def verifier.candidate.query_values
  (proof : Slice Std.U8) (p : verifier.Prepared) (a : verifier.Accumulator)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
  (obs : Option (verifier.Phase → Result Unit))
  (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) :
  Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
    verifier.Error)
  := do
  let i ← Array.index_usize p.queries a.next
  let u ← lift (UScalar.cast .Usize i)
  let q ← verifier.candidate.opening proof a.next
  let dots ← fast_dots.four_dots q g
  let i1 ← lift (Std.Usize.wrapping_mul 4#usize a.next)
  let we ← Array.index_usize dots 0#usize
  trace.value 9#u16 i1 we
  let i2 ← lift (Std.Usize.wrapping_mul 4#usize a.next)
  let i3 ← lift (Std.Usize.wrapping_add i2 1#usize)
  let we1 ← Array.index_usize dots 1#usize
  trace.value 9#u16 i3 we1
  let i4 ← lift (Std.Usize.wrapping_mul 4#usize a.next)
  let i5 ← lift (Std.Usize.wrapping_add i4 2#usize)
  let we2 ← Array.index_usize dots 2#usize
  trace.value 9#u16 i5 we2
  let i6 ← lift (Std.Usize.wrapping_mul 4#usize a.next)
  let i7 ← lift (Std.Usize.wrapping_add i6 3#usize)
  let we3 ← Array.index_usize dots 3#usize
  trace.value 9#u16 i7 we3
  let inverse ← verifier.QueryGeometry.for_query geometry a.next
  let we4 ← Array.index_usize p.alpha 0#usize
  let folded ← verifier.circle_fold_with_inverses we4 dots inverse
  let i8 ← lift (Std.Usize.wrapping_mul 2#usize a.next)
  trace.value 10#u16 i8 folded
  let values ←
    core.array.from_fn 4#usize
      verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
      q
  let i9 ← u % 4#usize
  let we5 ← Array.index_usize values i9
  let b ←
    core.cmp.PartialEq.ne.trait_default
      aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact
      folded we5
  if b
  then ok (core.result.Result.Err verifier.Error.Query)
  else
    let we6 ← Array.index_usize p.alpha 1#usize
    let folded1 ← verifier.line_fold_with_inverses we6 values inverse
    let i10 ← lift (Std.Usize.wrapping_mul 2#usize a.next)
    let i11 ← lift (Std.Usize.wrapping_add i10 1#usize)
    trace.value 10#u16 i11 folded1
    let i12 ← lift (Std.Usize.wrapping_sub a.next geometry.start)
    let z ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) geometry.line_z i12
    let m ← aspis_core.field.M31.mul z z
    let m1 ← aspis_core.field.M31.double m
    let m2 ← aspis_core.field.M31.ONE
    let node ← aspis_core.field.M31.sub m1 m2
    let (a1, pending1) ←
      verifier.accumulate_batched_with_node p a node folded1 pending
    verifier.mark obs (verifier.Phase.Query a.next)
    ok (core.result.Result.Ok (a1, pending1))
-/

end PRVFresh_C05_F08_RPz7_FIo_NativeFuns

theorem PRVEq.C05_F08.RPz7_FIo_NativeFuns.trace.value : @PRVFresh_C05_F08_RPz7_FIo_NativeFuns.trace.value = @FIo_Native.trace.value := by
  (trace "PRV-S1 PRVEq.C05_F08.RPz7_FIo_NativeFuns.trace.value"; rfl)
#print axioms PRVEq.C05_F08.RPz7_FIo_NativeFuns.trace.value

theorem PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.P : @PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.canonical.P = @FIo_Native.fast_pairing.canonical.P := by
  (trace "PRV-S2 PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.P"; delta PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.canonical.P FIo_Native.fast_pairing.canonical.P; try rfl; done)
#print axioms PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.P

theorem PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.reduce : @PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.canonical.reduce = @FIo_Native.fast_pairing.canonical.reduce := by
  (trace "PRV-S2 PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.reduce"; delta PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.canonical.reduce FIo_Native.fast_pairing.canonical.reduce; try simp only [PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.P]; try rfl; done)
#print axioms PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.reduce

theorem PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Dot.finish : @PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.canonical.Dot.finish = @FIo_Native.fast_pairing.canonical.Dot.finish := by
  (trace "PRV-S2 PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Dot.finish"; delta PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.canonical.Dot.finish FIo_Native.fast_pairing.canonical.Dot.finish; try simp only [PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.reduce]; try rfl; done)
#print axioms PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Dot.finish

theorem PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Q.limbs : @PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.canonical.Q.limbs = @FIo_Native.fast_pairing.canonical.Q.limbs := by
  (trace "PRV-S1 PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Q.limbs"; rfl)
#print axioms PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Q.limbs

theorem PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.EbyKDot.finish : @PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.EbyKDot.finish = @FIo_Native.fast_pairing.EbyKDot.finish := by
  (trace "PRV-S2 PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.EbyKDot.finish"; delta PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.EbyKDot.finish FIo_Native.fast_pairing.EbyKDot.finish; try simp only [PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Dot.finish, PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Q.limbs]; try rfl; done)
#print axioms PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.EbyKDot.finish

theorem PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.limbs_of : @PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.limbs_of = @FIo_Native.fast_pairing.limbs_of := by
  (trace "PRV-S1 PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.limbs_of"; rfl)
#print axioms PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.limbs_of

theorem PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Q.from_limbs : @PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.canonical.Q.from_limbs = @FIo_Native.fast_pairing.canonical.Q.from_limbs := by
  (trace "PRV-S2 PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Q.from_limbs"; delta PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.canonical.Q.from_limbs FIo_Native.fast_pairing.canonical.Q.from_limbs; try simp only [PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.P]; try rfl; done)
#print axioms PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Q.from_limbs

theorem PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.checked_q : @PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.checked_q = @FIo_Native.fast_pairing.checked_q := by
  (trace "PRV-S2 PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.checked_q"; delta PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.checked_q FIo_Native.fast_pairing.checked_q; try simp only [PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.limbs_of, PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Q.from_limbs]; try rfl; done)
#print axioms PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.checked_q

theorem PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.MAX_TERMS : @PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.MAX_TERMS = @FIo_Native.fast_pairing.MAX_TERMS := by
  (trace "PRV-S2 PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.MAX_TERMS"; delta PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.MAX_TERMS FIo_Native.fast_pairing.MAX_TERMS; try rfl; done)
#print axioms PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.MAX_TERMS

theorem PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Q.from_wide : @PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.canonical.Q.from_wide = @FIo_Native.fast_pairing.canonical.Q.from_wide := by
  (trace "PRV-S1 PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Q.from_wide"; rfl)
#print axioms PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Q.from_wide

theorem PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.EbyKDot.push : @PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.EbyKDot.push = @FIo_Native.fast_pairing.EbyKDot.push := by
  (trace "PRV-S2 PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.EbyKDot.push"; delta PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.EbyKDot.push FIo_Native.fast_pairing.EbyKDot.push; try simp only [PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.checked_q, PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.MAX_TERMS, PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Q.from_wide]; try rfl; done)
#print axioms PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.EbyKDot.push

theorem PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Dot.new : @PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.canonical.Dot.new = @FIo_Native.fast_pairing.canonical.Dot.new := by
  (trace "PRV-S1 PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Dot.new"; rfl)
#print axioms PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.canonical.Dot.new

theorem PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.EbyKDot.new : @PRVFresh_C05_F08_RPz7_FIo_NativeFuns.fast_pairing.EbyKDot.new = @FIo_Native.fast_pairing.EbyKDot.new := by
  (trace "PRV-S1 PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.EbyKDot.new"; rfl)
#print axioms PRVEq.C05_F08.RPz7_FIo_NativeFuns.fast_pairing.EbyKDot.new


end
end PRVBundle_8
section PRVBundle_9
-- GENERATED by PCUF_gen_equalities.py for gate module AspisC2HostEmbedding.Funs. Statements are against the gate constants of AspisC2HostEmbedding.Funs.
-- fresh emission: PCQF_aspis_core_field_a -> PRVFresh_C05_F09_AspisC2HostEmbedding_Funs; fresh source sha256 3fe20d1388c31691b3b9d5d799885592457170a7e0d68249d4fa5c9b3281a40a
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisC2HostEmbedding
namespace PRVFresh_C05_F09_AspisC2HostEmbedding_Funs

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::{aspis_core::field::QM31}::ZERO]
    Source: 'crates/aspis-core/src/field.rs', lines 869:4-878:6
    Visibility: public -/
@[global_simps, irreducible]
def field.QM31.ZERO : field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

end PRVFresh_C05_F09_AspisC2HostEmbedding_Funs
end AspisC2HostEmbedding

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F09.AspisC2HostEmbedding.Funs.field.P : @AspisC2HostEmbedding.PRVFresh_C05_F09_AspisC2HostEmbedding_Funs.field.P = @AspisC2HostEmbedding.field.P := by
  (trace "PRV-S2 PRVEq.C05_F09.AspisC2HostEmbedding.Funs.field.P"; delta AspisC2HostEmbedding.PRVFresh_C05_F09_AspisC2HostEmbedding_Funs.field.P AspisC2HostEmbedding.field.P; try rfl; done)
#print axioms PRVEq.C05_F09.AspisC2HostEmbedding.Funs.field.P

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F09.AspisC2HostEmbedding.Funs.field.QM31.ZERO : @AspisC2HostEmbedding.PRVFresh_C05_F09_AspisC2HostEmbedding_Funs.field.QM31.ZERO = @AspisC2HostEmbedding.field.QM31.ZERO := by
  (trace "PRV-S2 PRVEq.C05_F09.AspisC2HostEmbedding.Funs.field.QM31.ZERO"; delta AspisC2HostEmbedding.PRVFresh_C05_F09_AspisC2HostEmbedding_Funs.field.QM31.ZERO AspisC2HostEmbedding.field.QM31.ZERO; try rfl; done)
#print axioms PRVEq.C05_F09.AspisC2HostEmbedding.Funs.field.QM31.ZERO


end
end PRVBundle_9
section PRVBundle_10
-- GENERATED by PCUF_gen_equalities.py for gate module AspisR1CircleFallback.Types. Statements are against the gate constants of AspisR1CircleFallback.Types.
-- fresh emission: PCQF_aspis_r1_cost_probe_candidate -> PRVFresh_C05_F10_AspisR1CircleFallback_Types; fresh source sha256 95c2fb3bb0d1a2a15fd0d0fced330a4129dea4440f690d3d83b09258834a56be
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1CircleFallback
namespace PRVFresh_C05_F10_AspisR1CircleFallback_Types

/-- [aspis_core::field::M31]
    Source: 'crates/aspis-core/src/field.rs', lines 23:0-23:14
    Name pattern: [aspis_core::field::M31]
    Visibility: public -/
@[reducible]
def aspis_core.field.M31 := Std.U32

/-- [aspis_core::field::CM31]
    Source: 'crates/aspis-core/src/field.rs', lines 255:0-255:15
    Name pattern: [aspis_core::field::CM31]
    Visibility: public -/
structure aspis_core.field.CM31 where
  a : aspis_core.field.M31
  b : aspis_core.field.M31

/-- [aspis_core::field::QM31]
    Source: 'crates/aspis-core/src/field.rs', lines 432:0-432:15
    Name pattern: [aspis_core::field::QM31]
    Visibility: public -/
structure aspis_core.field.QM31 where
  c0 : aspis_core.field.CM31
  c1 : aspis_core.field.CM31

/-- [aspis_core::circle::SecureCirclePoint]
    Source: 'crates/aspis-core/src/circle.rs', lines 11:0-11:28
    Name pattern: [aspis_core::circle::SecureCirclePoint]
    Visibility: public -/
structure aspis_core.circle.SecureCirclePoint where
  x : aspis_core.field.QM31
  y : aspis_core.field.QM31

end PRVFresh_C05_F10_AspisR1CircleFallback_Types
end AspisR1CircleFallback

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.M31 : @AspisR1CircleFallback.PRVFresh_C05_F10_AspisR1CircleFallback_Types.aspis_core.field.M31 = @AspisR1CircleFallback.field.M31 := by
  (trace "PRV-S1 PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.M31"; rfl)
#print axioms PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.M31

set_option maxHeartbeats 200000 in
def PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.CM31.equiv : AspisR1CircleFallback.PRVFresh_C05_F10_AspisR1CircleFallback_Types.aspis_core.field.CM31 ≃ AspisR1CircleFallback.field.CM31 where
  toFun x := { a := x.a, b := x.b }
  invFun y := { a := y.a, b := y.b }
  left_inv x := by
    (trace "PRV-S1 PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.CM31"; cases x; rfl)
  right_inv y := by
    (trace "PRV-S1 PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.CM31"; cases y; rfl)
#print axioms PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.CM31.equiv

set_option maxHeartbeats 200000 in
def PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.QM31.equiv : AspisR1CircleFallback.PRVFresh_C05_F10_AspisR1CircleFallback_Types.aspis_core.field.QM31 ≃ AspisR1CircleFallback.field.QM31 where
  toFun x := { c0 := (PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.CM31.equiv x.c0), c1 := (PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.CM31.equiv x.c1) }
  invFun y := { c0 := (PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.CM31.equiv.symm y.c0), c1 := (PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.CM31.equiv.symm y.c1) }
  left_inv x := by
    (trace "PRV-S1 PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.QM31"; cases x; rfl)
  right_inv y := by
    (trace "PRV-S1 PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.QM31"; cases y; rfl)
#print axioms PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.QM31.equiv

set_option maxHeartbeats 200000 in
def PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.circle.SecureCirclePoint.equiv : AspisR1CircleFallback.PRVFresh_C05_F10_AspisR1CircleFallback_Types.aspis_core.circle.SecureCirclePoint ≃ AspisR1CircleFallback.circle.SecureCirclePoint where
  toFun x := { x := (PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.QM31.equiv x.x), y := (PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.QM31.equiv x.y) }
  invFun y := { x := (PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.QM31.equiv.symm y.x), y := (PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.field.QM31.equiv.symm y.y) }
  left_inv x := by
    (trace "PRV-S1 PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.circle.SecureCirclePoint"; cases x; rfl)
  right_inv y := by
    (trace "PRV-S1 PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.circle.SecureCirclePoint"; cases y; rfl)
#print axioms PRVEq.C05_F10.AspisR1CircleFallback.Types.aspis_core.circle.SecureCirclePoint.equiv


end PRVBundle_10
section PRVBundle_11
-- GENERATED by PCUF_gen_equalities.py for gate module AspisR1CircleSampleWrapper.Types. Statements are against the gate constants of AspisR1CircleSampleWrapper.Types.
-- fresh emission: PCQF_aspis_r1_cost_probe_candidate -> PRVFresh_C05_F11_AspisR1CircleSampleWrapper_Types; fresh source sha256 95c2fb3bb0d1a2a15fd0d0fced330a4129dea4440f690d3d83b09258834a56be
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1CircleSampleWrapper
namespace PRVFresh_C05_F11_AspisR1CircleSampleWrapper_Types

/-- [aspis_core::field::M31]
    Source: 'crates/aspis-core/src/field.rs', lines 23:0-23:14
    Name pattern: [aspis_core::field::M31]
    Visibility: public -/
@[reducible]
def aspis_core.field.M31 := Std.U32

/-- [aspis_core::field::CM31]
    Source: 'crates/aspis-core/src/field.rs', lines 255:0-255:15
    Name pattern: [aspis_core::field::CM31]
    Visibility: public -/
structure aspis_core.field.CM31 where
  a : aspis_core.field.M31
  b : aspis_core.field.M31

/-- [aspis_core::field::QM31]
    Source: 'crates/aspis-core/src/field.rs', lines 432:0-432:15
    Name pattern: [aspis_core::field::QM31]
    Visibility: public -/
structure aspis_core.field.QM31 where
  c0 : aspis_core.field.CM31
  c1 : aspis_core.field.CM31

/-- [aspis_core::circle::SecureCirclePoint]
    Source: 'crates/aspis-core/src/circle.rs', lines 11:0-11:28
    Name pattern: [aspis_core::circle::SecureCirclePoint]
    Visibility: public -/
structure aspis_core.circle.SecureCirclePoint where
  x : aspis_core.field.QM31
  y : aspis_core.field.QM31

end PRVFresh_C05_F11_AspisR1CircleSampleWrapper_Types
end AspisR1CircleSampleWrapper

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.M31 : @AspisR1CircleSampleWrapper.PRVFresh_C05_F11_AspisR1CircleSampleWrapper_Types.aspis_core.field.M31 = @AspisR1CircleSampleWrapper.field.M31 := by
  (trace "PRV-S1 PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.M31"; rfl)
#print axioms PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.M31

set_option maxHeartbeats 200000 in
def PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.CM31.equiv : AspisR1CircleSampleWrapper.PRVFresh_C05_F11_AspisR1CircleSampleWrapper_Types.aspis_core.field.CM31 ≃ AspisR1CircleSampleWrapper.field.CM31 where
  toFun x := { a := x.a, b := x.b }
  invFun y := { a := y.a, b := y.b }
  left_inv x := by
    (trace "PRV-S1 PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.CM31"; cases x; rfl)
  right_inv y := by
    (trace "PRV-S1 PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.CM31"; cases y; rfl)
#print axioms PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.CM31.equiv

set_option maxHeartbeats 200000 in
def PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.QM31.equiv : AspisR1CircleSampleWrapper.PRVFresh_C05_F11_AspisR1CircleSampleWrapper_Types.aspis_core.field.QM31 ≃ AspisR1CircleSampleWrapper.field.QM31 where
  toFun x := { c0 := (PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.CM31.equiv x.c0), c1 := (PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.CM31.equiv x.c1) }
  invFun y := { c0 := (PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.CM31.equiv.symm y.c0), c1 := (PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.CM31.equiv.symm y.c1) }
  left_inv x := by
    (trace "PRV-S1 PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.QM31"; cases x; rfl)
  right_inv y := by
    (trace "PRV-S1 PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.QM31"; cases y; rfl)
#print axioms PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.QM31.equiv

set_option maxHeartbeats 200000 in
def PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.circle.SecureCirclePoint.equiv : AspisR1CircleSampleWrapper.PRVFresh_C05_F11_AspisR1CircleSampleWrapper_Types.aspis_core.circle.SecureCirclePoint ≃ AspisR1CircleSampleWrapper.circle.SecureCirclePoint where
  toFun x := { x := (PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.QM31.equiv x.x), y := (PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.QM31.equiv x.y) }
  invFun y := { x := (PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.QM31.equiv.symm y.x), y := (PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.field.QM31.equiv.symm y.y) }
  left_inv x := by
    (trace "PRV-S1 PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.circle.SecureCirclePoint"; cases x; rfl)
  right_inv y := by
    (trace "PRV-S1 PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.circle.SecureCirclePoint"; cases y; rfl)
#print axioms PRVEq.C05_F11.AspisR1CircleSampleWrapper.Types.aspis_core.circle.SecureCirclePoint.equiv


end PRVBundle_11
section PRVBundle_12
-- GENERATED by PCUF_gen_equalities.py for gate module AspisR1CurrentWide.Funs. Statements are against the gate constants of AspisR1CurrentWide.Funs.
-- fresh emission: PCQF_aspis_core_field_a -> PRVFresh_C05_F12_AspisR1CurrentWide_Funs; fresh source sha256 3fe20d1388c31691b3b9d5d799885592457170a7e0d68249d4fa5c9b3281a40a
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1CurrentWide
namespace PRVFresh_C05_F12_AspisR1CurrentWide_Funs

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 31:0-44:1 -/
def field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 field.P)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← lift (UScalar.cast .U64 field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= field.P
  then x3 - field.P
  else ok x3

/-- [aspis_core::field::{aspis_core::field::M31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 62:4-88:5
    Visibility: public -/
def field.M31.add (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let s ← self + rhs
  if s >= field.P
  then let s1 ← s - field.P
       ok s1
  else ok s

/-- [aspis_core::field::{aspis_core::field::M31}::sub]:
    Source: 'crates/aspis-core/src/field.rs', lines 94:4-119:5
    Visibility: public -/
def field.M31.sub (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← self + field.P
  let s ← i - rhs
  if s >= field.P
  then let s1 ← s - field.P
       ok s1
  else ok s

/-- [aspis_core::field::{aspis_core::field::M31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 133:4-137:5
    Visibility: public -/
def field.M31.mul (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← i * i1
  let i3 ← field.reduce_u64 i2
  ok i3

/-- [aspis_core::field::{aspis_core::field::M31}::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 153:4-155:5
    Visibility: public -/
def field.M31.reduce_u64 (value : Std.U64) : Result field.M31 := do
  let i ← field.reduce_u64 value
  ok i

/-- [aspis_core::field::{aspis_core::field::M31}::double]:
    Source: 'crates/aspis-core/src/field.rs', lines 183:4-185:5
    Visibility: public -/
def field.M31.double (self : field.M31) : Result field.M31 := do
  field.M31.add self self

/-- [aspis_core::field::{aspis_core::field::CM31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 281:4-286:5
    Visibility: public -/
def field.CM31.add
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m ← field.M31.add self.a rhs.a
  let m1 ← field.M31.add self.b rhs.b
  ok { a := m, b := m1 }

/-- [aspis_core::field::{aspis_core::field::CM31}::sub]:
    Source: 'crates/aspis-core/src/field.rs', lines 289:4-294:5
    Visibility: public -/
def field.CM31.sub
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m ← field.M31.sub self.a rhs.a
  let m1 ← field.M31.sub self.b rhs.b
  ok { a := m, b := m1 }

/-- [aspis_core::field::{aspis_core::field::CM31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 306:4-320:5
    Visibility: public -/
def field.CM31.mul
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m0 ← field.M31.mul self.a rhs.a
  let m1 ← field.M31.mul self.b rhs.b
  let i := self.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i1 + i3
  let i5 := rhs.a
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.b
  let i8 ← lift (core.convert.num.FromU64U32.from i7)
  let i9 ← i6 + i8
  let i10 ← i4 * i9
  let m2 ← field.M31.reduce_u64 i10
  let m ← field.M31.sub m0 m1
  let m3 ← field.M31.sub m2 m0
  let m4 ← field.M31.sub m3 m1
  ok { a := m, b := m4 }

/-- [aspis_core::field::{aspis_core::field::CM31}::mul_m31]:
    Source: 'crates/aspis-core/src/field.rs', lines 338:4-343:5
    Visibility: public -/
def field.CM31.mul_m31
  (self : field.CM31) (rhs : field.M31) : Result field.CM31 := do
  let m ← field.M31.mul self.a rhs
  let m1 ← field.M31.mul self.b rhs
  ok { a := m, b := m1 }

/-- [aspis_core::field::mul_by_r]:
    Source: 'crates/aspis-core/src/field.rs', lines 860:0-866:1 -/
def field.mul_by_r (x : field.CM31) : Result field.CM31 := do
  let m ← field.M31.double x.a
  let m1 ← field.M31.sub m x.b
  let m2 ← field.M31.double x.b
  let m3 ← field.M31.add x.a m2
  ok { a := m1, b := m3 }

/-- [aspis_core::field::{aspis_core::field::QM31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 896:4-903:5
    Visibility: public -/
def field.QM31.add
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let c ← field.CM31.add self.c0 rhs.c0
  let c1 ← field.CM31.add self.c1 rhs.c1
  ok { c0 := c, c1 }

/-- [aspis_core::field::{aspis_core::field::QM31}::sub]:
    Source: 'crates/aspis-core/src/field.rs', lines 906:4-913:5
    Visibility: public -/
def field.QM31.sub
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let c ← field.CM31.sub self.c0 rhs.c0
  let c1 ← field.CM31.sub self.c1 rhs.c1
  ok { c0 := c, c1 }

/-- [aspis_core::field::{aspis_core::field::QM31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 935:4-945:5
    Visibility: public -/
def field.QM31.mul
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let m0 ← field.CM31.mul self.c0 rhs.c0
  let m1 ← field.CM31.mul self.c1 rhs.c1
  let c ← field.CM31.add self.c0 self.c1
  let c1 ← field.CM31.add rhs.c0 rhs.c1
  let m2 ← field.CM31.mul c c1
  let c2 ← field.mul_by_r m1
  let c3 ← field.CM31.add m0 c2
  let c4 ← field.CM31.sub m2 m0
  let c5 ← field.CM31.sub c4 m1
  ok { c0 := c3, c1 := c5 }

/-- [aspis_core::field::{aspis_core::field::QM31}::mul_m31]:
    Source: 'crates/aspis-core/src/field.rs', lines 975:4-982:5
    Visibility: public -/
def field.QM31.mul_m31
  (self : field.QM31) (rhs : field.M31) : Result field.QM31 := do
  let c ← field.CM31.mul_m31 self.c0 rhs
  let c1 ← field.CM31.mul_m31 self.c1 rhs
  ok { c0 := c, c1 }

end PRVFresh_C05_F12_AspisR1CurrentWide_Funs
end AspisR1CurrentWide

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.P : @AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.P = @AspisR1CurrentWide.field.P := by
  (trace "PRV-S2 PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.P"; delta AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.P AspisR1CurrentWide.field.P; try rfl; done)
#print axioms PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.P

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.reduce_u64 : @AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.reduce_u64 = @AspisR1CurrentWide.field.reduce_u64 := by
  (trace "PRV-S2 PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.reduce_u64"; delta AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.reduce_u64 AspisR1CurrentWide.field.reduce_u64; try simp only [PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.P]; try rfl; done)
#print axioms PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.reduce_u64

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.add : @AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.M31.add = @AspisR1CurrentWide.field.M31.add := by
  (trace "PRV-S2 PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.add"; delta AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.M31.add AspisR1CurrentWide.field.M31.add; try simp only [PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.P]; try rfl; done)
#print axioms PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.add

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.sub : @AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.M31.sub = @AspisR1CurrentWide.field.M31.sub := by
  (trace "PRV-S2 PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.sub"; delta AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.M31.sub AspisR1CurrentWide.field.M31.sub; try simp only [PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.P]; try rfl; done)
#print axioms PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.sub

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.mul : @AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.M31.mul = @AspisR1CurrentWide.field.M31.mul := by
  (trace "PRV-S2 PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.mul"; delta AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.M31.mul AspisR1CurrentWide.field.M31.mul; try simp only [PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.reduce_u64]; try rfl; done)
#print axioms PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.mul

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.reduce_u64 : @AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.M31.reduce_u64 = @AspisR1CurrentWide.field.M31.reduce_u64 := by
  (trace "PRV-S2 PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.reduce_u64"; delta AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.M31.reduce_u64 AspisR1CurrentWide.field.M31.reduce_u64; try simp only [PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.reduce_u64]; try rfl; done)
#print axioms PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.reduce_u64

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.double : @AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.M31.double = @AspisR1CurrentWide.field.M31.double := by
  (trace "PRV-S2 PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.double"; delta AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.M31.double AspisR1CurrentWide.field.M31.double; try simp only [PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.add]; try rfl; done)
#print axioms PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.double

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.add : @AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.CM31.add = @AspisR1CurrentWide.field.CM31.add := by
  (trace "PRV-S2 PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.add"; delta AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.CM31.add AspisR1CurrentWide.field.CM31.add; try simp only [PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.add]; try rfl; done)
#print axioms PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.add

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.sub : @AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.CM31.sub = @AspisR1CurrentWide.field.CM31.sub := by
  (trace "PRV-S2 PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.sub"; delta AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.CM31.sub AspisR1CurrentWide.field.CM31.sub; try simp only [PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.sub]; try rfl; done)
#print axioms PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.sub

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.mul : @AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.CM31.mul = @AspisR1CurrentWide.field.CM31.mul := by
  (trace "PRV-S2 PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.mul"; delta AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.CM31.mul AspisR1CurrentWide.field.CM31.mul; try simp only [PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.sub, PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.mul, PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.reduce_u64]; try rfl; done)
#print axioms PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.mul

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.mul_m31 : @AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.CM31.mul_m31 = @AspisR1CurrentWide.field.CM31.mul_m31 := by
  (trace "PRV-S2 PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.mul_m31"; delta AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.CM31.mul_m31 AspisR1CurrentWide.field.CM31.mul_m31; try simp only [PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.mul]; try rfl; done)
#print axioms PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.mul_m31

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.mul_by_r : @AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.mul_by_r = @AspisR1CurrentWide.field.mul_by_r := by
  (trace "PRV-S2 PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.mul_by_r"; delta AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.mul_by_r AspisR1CurrentWide.field.mul_by_r; try simp only [PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.add, PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.sub, PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.M31.double]; try rfl; done)
#print axioms PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.mul_by_r

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.QM31.add : @AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.QM31.add = @AspisR1CurrentWide.field.QM31.add := by
  (trace "PRV-S2 PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.QM31.add"; delta AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.QM31.add AspisR1CurrentWide.field.QM31.add; try simp only [PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.add]; try rfl; done)
#print axioms PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.QM31.add

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.QM31.sub : @AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.QM31.sub = @AspisR1CurrentWide.field.QM31.sub := by
  (trace "PRV-S2 PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.QM31.sub"; delta AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.QM31.sub AspisR1CurrentWide.field.QM31.sub; try simp only [PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.sub]; try rfl; done)
#print axioms PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.QM31.sub

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.QM31.mul : @AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.QM31.mul = @AspisR1CurrentWide.field.QM31.mul := by
  (trace "PRV-S2 PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.QM31.mul"; delta AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.QM31.mul AspisR1CurrentWide.field.QM31.mul; try simp only [PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.add, PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.sub, PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.mul, PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.mul_by_r]; try rfl; done)
#print axioms PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.QM31.mul

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.QM31.mul_m31 : @AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.QM31.mul_m31 = @AspisR1CurrentWide.field.QM31.mul_m31 := by
  (trace "PRV-S2 PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.QM31.mul_m31"; delta AspisR1CurrentWide.PRVFresh_C05_F12_AspisR1CurrentWide_Funs.field.QM31.mul_m31 AspisR1CurrentWide.field.QM31.mul_m31; try simp only [PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.CM31.mul_m31]; try rfl; done)
#print axioms PRVEq.C05_F12.AspisR1CurrentWide.Funs.field.QM31.mul_m31


end
end PRVBundle_12
section PRVBundle_13
-- GENERATED by PCUF_gen_equalities.py for gate module AspisR1Post25Sampler.Funs. Statements are against the gate constants of AspisR1Post25Sampler.Funs.
-- fresh emission: PCQF_aspis_core_field_a -> PRVFresh_C05_F13_AspisR1Post25Sampler_Funs; fresh source sha256 3fe20d1388c31691b3b9d5d799885592457170a7e0d68249d4fa5c9b3281a40a
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1Post25Sampler
namespace PRVFresh_C05_F13_AspisR1Post25Sampler_Funs

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::{aspis_core::field::CM31}::new]:
    Source: 'crates/aspis-core/src/field.rs', lines 271:4-273:5
    Visibility: public -/
def field.CM31.new (a : field.M31) (b : field.M31) : Result field.CM31 := do
  ok { a, b }

end PRVFresh_C05_F13_AspisR1Post25Sampler_Funs
end AspisR1Post25Sampler

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F13.AspisR1Post25Sampler.Funs.field.P : @AspisR1Post25Sampler.PRVFresh_C05_F13_AspisR1Post25Sampler_Funs.field.P = @AspisR1Post25Sampler.field.P := by
  (trace "PRV-S2 PRVEq.C05_F13.AspisR1Post25Sampler.Funs.field.P"; delta AspisR1Post25Sampler.PRVFresh_C05_F13_AspisR1Post25Sampler_Funs.field.P AspisR1Post25Sampler.field.P; try rfl; done)
#print axioms PRVEq.C05_F13.AspisR1Post25Sampler.Funs.field.P

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F13.AspisR1Post25Sampler.Funs.field.CM31.new : @AspisR1Post25Sampler.PRVFresh_C05_F13_AspisR1Post25Sampler_Funs.field.CM31.new = @AspisR1Post25Sampler.field.CM31.new := by
  (trace "PRV-S1 PRVEq.C05_F13.AspisR1Post25Sampler.Funs.field.CM31.new"; rfl)
#print axioms PRVEq.C05_F13.AspisR1Post25Sampler.Funs.field.CM31.new


end
end PRVBundle_13
section PRVBundle_14
-- GENERATED by PCUF_gen_equalities.py for gate module AspisR1PrefixAggregateParser.Funs. Statements are against the gate constants of AspisR1PrefixAggregateParser.Funs.
-- fresh emission: PCQF_aspis_core_field_a -> PRVFresh_C05_F14_AspisR1PrefixAggregateParser_Funs; fresh source sha256 3fe20d1388c31691b3b9d5d799885592457170a7e0d68249d4fa5c9b3281a40a
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1PrefixAggregateParser
namespace PRVFresh_C05_F14_AspisR1PrefixAggregateParser_Funs

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::{aspis_core::field::QM31}::ZERO]
    Source: 'crates/aspis-core/src/field.rs', lines 869:4-878:6
    Visibility: public -/
@[global_simps, irreducible]
def field.QM31.ZERO : field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

end PRVFresh_C05_F14_AspisR1PrefixAggregateParser_Funs
end AspisR1PrefixAggregateParser

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F14.AspisR1PrefixAggregateParser.Funs.field.P : @AspisR1PrefixAggregateParser.PRVFresh_C05_F14_AspisR1PrefixAggregateParser_Funs.field.P = @AspisR1PrefixAggregateParser.field.P := by
  (trace "PRV-S2 PRVEq.C05_F14.AspisR1PrefixAggregateParser.Funs.field.P"; delta AspisR1PrefixAggregateParser.PRVFresh_C05_F14_AspisR1PrefixAggregateParser_Funs.field.P AspisR1PrefixAggregateParser.field.P; try rfl; done)
#print axioms PRVEq.C05_F14.AspisR1PrefixAggregateParser.Funs.field.P

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F14.AspisR1PrefixAggregateParser.Funs.field.QM31.ZERO : @AspisR1PrefixAggregateParser.PRVFresh_C05_F14_AspisR1PrefixAggregateParser_Funs.field.QM31.ZERO = @AspisR1PrefixAggregateParser.field.QM31.ZERO := by
  (trace "PRV-S2 PRVEq.C05_F14.AspisR1PrefixAggregateParser.Funs.field.QM31.ZERO"; delta AspisR1PrefixAggregateParser.PRVFresh_C05_F14_AspisR1PrefixAggregateParser_Funs.field.QM31.ZERO AspisR1PrefixAggregateParser.field.QM31.ZERO; try rfl; done)
#print axioms PRVEq.C05_F14.AspisR1PrefixAggregateParser.Funs.field.QM31.ZERO


end
end PRVBundle_14
section PRVBundle_15
-- GENERATED by PCUF_gen_equalities.py for gate module AspisR1PublicPreparation.Types. Statements are against the gate constants of AspisR1PublicPreparation.Types.
-- fresh emission: PCQE_aspis_statement_pool_v1_pair_forest_terminal -> PRVFresh_C05_F15_AspisR1PublicPreparation_Types; fresh source sha256 c7af3f9d94f5cad1f1e03279ec760c935a514076ce366e244531be54da334193
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1PublicPreparation
namespace PRVFresh_C05_F15_AspisR1PublicPreparation_Types

/-- [aspis_core::field::M31]
    Source: 'crates/aspis-core/src/field.rs', lines 23:0-23:14
    Name pattern: [aspis_core::field::M31]
    Visibility: public -/
@[reducible]
def aspis_core.field.M31 := Std.U32

/-- [aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs', lines 404:0-411:1
    Visibility: public -/
structure pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  sequence : Std.U64
  next_pair_index : Std.U64
  current_root : Array aspis_core.field.M31 8#usize
  frontier : Array (Array aspis_core.field.M31 8#usize) 20#usize

/-- [aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_terminal.rs', lines 116:0-120:1
    Visibility: public -/
structure pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 where
  next_pair_index : Std.U64
  next_root : Array aspis_core.field.M31 8#usize
  next_frontier : Array (Array aspis_core.field.M31 8#usize) 20#usize

/-- [aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs', lines 414:0-419:1
    Visibility: public -/
structure pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 where
  live_snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
  candidate_afterstate : pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1

/-- [aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalCommonV1]
    Source: 'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs', lines 93:0-103:1
    Visibility: public -/
structure pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 where
  master_account : Array Std.U8 32#usize
  checkpoint_account : Array Std.U8 32#usize
  selected_lane_account : Array Std.U8 32#usize
  output_lane : Std.U8
  checkpoint_sequence : Std.U64
  historical_global_anchor : Array aspis_core.field.M31 8#usize
  lane_transition : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1

/-- [aspis_statement::pool_v1::payment_relation::PoolV1WithdrawalPublicV1]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 58:0-68:1
    Visibility: public -/
structure pool_v1.payment_relation.PoolV1WithdrawalPublicV1 where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor_sequence : Std.U64
  anchor_root : Array aspis_core.field.M31 8#usize
  nullifier : Array aspis_core.field.M31 8#usize
  asset_id : aspis_core.field.M31
  amount : Std.U32
  destination_token_account : Array Std.U8 32#usize
  change_commitment : Array aspis_core.field.M31 8#usize

/-- [aspis_statement::pool_v1::payment_relation::PoolV1PrivateTransferPublicV1]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 46:0-55:1
    Visibility: public -/
structure pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor_sequence : Std.U64
  anchor_root : Array aspis_core.field.M31 8#usize
  nullifier : Array aspis_core.field.M31 8#usize
  asset_id : aspis_core.field.M31
  recipient_commitment : Array aspis_core.field.M31 8#usize
  change_commitment : Array aspis_core.field.M31 8#usize

end PRVFresh_C05_F15_AspisR1PublicPreparation_Types
end AspisR1PublicPreparation

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F15.AspisR1PublicPreparation.Types.aspis_core.field.M31 : @AspisR1PublicPreparation.PRVFresh_C05_F15_AspisR1PublicPreparation_Types.aspis_core.field.M31 = @AspisR1PublicPreparation.aspis_core.field.M31 := by
  (trace "PRV-S1 PRVEq.C05_F15.AspisR1PublicPreparation.Types.aspis_core.field.M31"; rfl)
#print axioms PRVEq.C05_F15.AspisR1PublicPreparation.Types.aspis_core.field.M31

set_option maxHeartbeats 200000 in
def PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1.equiv : AspisR1PublicPreparation.PRVFresh_C05_F15_AspisR1PublicPreparation_Types.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 ≃ AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 where
  toFun x := { pool := x.pool, deployment_domain := x.deployment_domain, sequence := x.sequence, next_pair_index := x.next_pair_index, current_root := x.current_root, frontier := x.frontier }
  invFun y := { pool := y.pool, deployment_domain := y.deployment_domain, sequence := y.sequence, next_pair_index := y.next_pair_index, current_root := y.current_root, frontier := y.frontier }
  left_inv x := by
    (trace "PRV-S1 PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1"; cases x; rfl)
  right_inv y := by
    (trace "PRV-S1 PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1"; cases y; rfl)
#print axioms PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1.equiv

set_option maxHeartbeats 200000 in
def PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.equiv : AspisR1PublicPreparation.PRVFresh_C05_F15_AspisR1PublicPreparation_Types.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 ≃ AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 where
  toFun x := { next_pair_index := x.next_pair_index, next_root := x.next_root, next_frontier := x.next_frontier }
  invFun y := { next_pair_index := y.next_pair_index, next_root := y.next_root, next_frontier := y.next_frontier }
  left_inv x := by
    (trace "PRV-S1 PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1"; cases x; rfl)
  right_inv y := by
    (trace "PRV-S1 PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1"; cases y; rfl)
#print axioms PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.equiv

set_option maxHeartbeats 200000 in
def PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.equiv : AspisR1PublicPreparation.PRVFresh_C05_F15_AspisR1PublicPreparation_Types.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 ≃ AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 where
  toFun x := { live_snapshot := (PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1.equiv x.live_snapshot), candidate_afterstate := (PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.equiv x.candidate_afterstate) }
  invFun y := { live_snapshot := (PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1.equiv.symm y.live_snapshot), candidate_afterstate := (PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1.equiv.symm y.candidate_afterstate) }
  left_inv x := by
    (trace "PRV-S1 PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1"; cases x; rfl)
  right_inv y := by
    (trace "PRV-S1 PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1"; cases y; rfl)
#print axioms PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.equiv

set_option maxHeartbeats 200000 in
def PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1.equiv : AspisR1PublicPreparation.PRVFresh_C05_F15_AspisR1PublicPreparation_Types.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 ≃ AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 where
  toFun x := { master_account := x.master_account, checkpoint_account := x.checkpoint_account, selected_lane_account := x.selected_lane_account, output_lane := x.output_lane, checkpoint_sequence := x.checkpoint_sequence, historical_global_anchor := x.historical_global_anchor, lane_transition := (PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.equiv x.lane_transition) }
  invFun y := { master_account := y.master_account, checkpoint_account := y.checkpoint_account, selected_lane_account := y.selected_lane_account, output_lane := y.output_lane, checkpoint_sequence := y.checkpoint_sequence, historical_global_anchor := y.historical_global_anchor, lane_transition := (PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.equiv.symm y.lane_transition) }
  left_inv x := by
    (trace "PRV-S1 PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1"; cases x; rfl)
  right_inv y := by
    (trace "PRV-S1 PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1"; cases y; rfl)
#print axioms PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1.equiv

set_option maxHeartbeats 200000 in
def PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.payment_relation.PoolV1WithdrawalPublicV1.equiv : AspisR1PublicPreparation.PRVFresh_C05_F15_AspisR1PublicPreparation_Types.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 ≃ AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 where
  toFun x := { pool := x.pool, deployment_domain := x.deployment_domain, anchor_sequence := x.anchor_sequence, anchor_root := x.anchor_root, nullifier := x.nullifier, asset_id := x.asset_id, amount := x.amount, destination_token_account := x.destination_token_account, change_commitment := x.change_commitment }
  invFun y := { pool := y.pool, deployment_domain := y.deployment_domain, anchor_sequence := y.anchor_sequence, anchor_root := y.anchor_root, nullifier := y.nullifier, asset_id := y.asset_id, amount := y.amount, destination_token_account := y.destination_token_account, change_commitment := y.change_commitment }
  left_inv x := by
    (trace "PRV-S1 PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.payment_relation.PoolV1WithdrawalPublicV1"; cases x; rfl)
  right_inv y := by
    (trace "PRV-S1 PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.payment_relation.PoolV1WithdrawalPublicV1"; cases y; rfl)
#print axioms PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.payment_relation.PoolV1WithdrawalPublicV1.equiv

set_option maxHeartbeats 200000 in
def PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1.equiv : AspisR1PublicPreparation.PRVFresh_C05_F15_AspisR1PublicPreparation_Types.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 ≃ AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 where
  toFun x := { pool := x.pool, deployment_domain := x.deployment_domain, anchor_sequence := x.anchor_sequence, anchor_root := x.anchor_root, nullifier := x.nullifier, asset_id := x.asset_id, recipient_commitment := x.recipient_commitment, change_commitment := x.change_commitment }
  invFun y := { pool := y.pool, deployment_domain := y.deployment_domain, anchor_sequence := y.anchor_sequence, anchor_root := y.anchor_root, nullifier := y.nullifier, asset_id := y.asset_id, recipient_commitment := y.recipient_commitment, change_commitment := y.change_commitment }
  left_inv x := by
    (trace "PRV-S1 PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1"; cases x; rfl)
  right_inv y := by
    (trace "PRV-S1 PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1"; cases y; rfl)
#print axioms PRVEq.C05_F15.AspisR1PublicPreparation.Types.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1.equiv


end PRVBundle_15
section PRVBundle_16
-- GENERATED by PCUF_gen_equalities.py for gate module AspisR1Qm31SamplerIndex.Funs. Statements are against the gate constants of AspisR1Qm31SamplerIndex.Funs.
-- fresh emission: PCQF_aspis_core_field_a -> PRVFresh_C05_F16_AspisR1Qm31SamplerIndex_Funs; fresh source sha256 3fe20d1388c31691b3b9d5d799885592457170a7e0d68249d4fa5c9b3281a40a
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1Qm31SamplerIndex
namespace PRVFresh_C05_F16_AspisR1Qm31SamplerIndex_Funs

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::{aspis_core::field::CM31}::new]:
    Source: 'crates/aspis-core/src/field.rs', lines 271:4-273:5
    Visibility: public -/
def field.CM31.new (a : field.M31) (b : field.M31) : Result field.CM31 := do
  ok { a, b }

end PRVFresh_C05_F16_AspisR1Qm31SamplerIndex_Funs
end AspisR1Qm31SamplerIndex

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F16.AspisR1Qm31SamplerIndex.Funs.field.P : @AspisR1Qm31SamplerIndex.PRVFresh_C05_F16_AspisR1Qm31SamplerIndex_Funs.field.P = @AspisR1Qm31SamplerIndex.field.P := by
  (trace "PRV-S2 PRVEq.C05_F16.AspisR1Qm31SamplerIndex.Funs.field.P"; delta AspisR1Qm31SamplerIndex.PRVFresh_C05_F16_AspisR1Qm31SamplerIndex_Funs.field.P AspisR1Qm31SamplerIndex.field.P; try rfl; done)
#print axioms PRVEq.C05_F16.AspisR1Qm31SamplerIndex.Funs.field.P

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F16.AspisR1Qm31SamplerIndex.Funs.field.CM31.new : @AspisR1Qm31SamplerIndex.PRVFresh_C05_F16_AspisR1Qm31SamplerIndex_Funs.field.CM31.new = @AspisR1Qm31SamplerIndex.field.CM31.new := by
  (trace "PRV-S1 PRVEq.C05_F16.AspisR1Qm31SamplerIndex.Funs.field.CM31.new"; rfl)
#print axioms PRVEq.C05_F16.AspisR1Qm31SamplerIndex.Funs.field.CM31.new


end
end PRVBundle_16
section PRVBundle_17
-- GENERATED by PCUF_gen_equalities.py for gate module AspisR1SemanticCallExtraction.Funs. Statements are against the gate constants of AspisR1SemanticCallExtraction.Funs.
-- fresh emission: PCQF_aspis_core_field_a -> PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs; fresh source sha256 3fe20d1388c31691b3b9d5d799885592457170a7e0d68249d4fa5c9b3281a40a
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1SemanticCallExtraction
namespace PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs
/- PRVE name-map (prefix aspis_core.): fresh bare names of the aspis-core crate resolve to the gate names under AspisR1SemanticCallExtraction.aspis_core -/
open AspisR1SemanticCallExtraction.aspis_core

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 31:0-44:1 -/
def field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 field.P)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← lift (UScalar.cast .U64 field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= field.P
  then x3 - field.P
  else ok x3

/-- [aspis_core::field::{aspis_core::field::M31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 62:4-88:5
    Visibility: public -/
def field.M31.add (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let s ← self + rhs
  if s >= field.P
  then let s1 ← s - field.P
       ok s1
  else ok s

/-- [aspis_core::field::{aspis_core::field::M31}::sub]:
    Source: 'crates/aspis-core/src/field.rs', lines 94:4-119:5
    Visibility: public -/
def field.M31.sub (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← self + field.P
  let s ← i - rhs
  if s >= field.P
  then let s1 ← s - field.P
       ok s1
  else ok s

/-- [aspis_core::field::{aspis_core::field::M31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 133:4-137:5
    Visibility: public -/
def field.M31.mul (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← i * i1
  let i3 ← field.reduce_u64 i2
  ok i3

/-- [aspis_core::field::{aspis_core::field::M31}::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 153:4-155:5
    Visibility: public -/
def field.M31.reduce_u64 (value : Std.U64) : Result field.M31 := do
  let i ← field.reduce_u64 value
  ok i

/-- [aspis_core::field::{aspis_core::field::M31}::double]:
    Source: 'crates/aspis-core/src/field.rs', lines 183:4-185:5
    Visibility: public -/
def field.M31.double (self : field.M31) : Result field.M31 := do
  field.M31.add self self

/-- [aspis_core::field::{aspis_core::field::CM31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 281:4-286:5
    Visibility: public -/
def field.CM31.add
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m ← field.M31.add self.a rhs.a
  let m1 ← field.M31.add self.b rhs.b
  ok { a := m, b := m1 }

/-- [aspis_core::field::{aspis_core::field::CM31}::sub]:
    Source: 'crates/aspis-core/src/field.rs', lines 289:4-294:5
    Visibility: public -/
def field.CM31.sub
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m ← field.M31.sub self.a rhs.a
  let m1 ← field.M31.sub self.b rhs.b
  ok { a := m, b := m1 }

/-- [aspis_core::field::{aspis_core::field::CM31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 306:4-320:5
    Visibility: public -/
def field.CM31.mul
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m0 ← field.M31.mul self.a rhs.a
  let m1 ← field.M31.mul self.b rhs.b
  let i := self.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i1 + i3
  let i5 := rhs.a
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.b
  let i8 ← lift (core.convert.num.FromU64U32.from i7)
  let i9 ← i6 + i8
  let i10 ← i4 * i9
  let m2 ← field.M31.reduce_u64 i10
  let m ← field.M31.sub m0 m1
  let m3 ← field.M31.sub m2 m0
  let m4 ← field.M31.sub m3 m1
  ok { a := m, b := m4 }

/-- [aspis_core::field::mul_by_r]:
    Source: 'crates/aspis-core/src/field.rs', lines 860:0-866:1 -/
def field.mul_by_r (x : field.CM31) : Result field.CM31 := do
  let m ← field.M31.double x.a
  let m1 ← field.M31.sub m x.b
  let m2 ← field.M31.double x.b
  let m3 ← field.M31.add x.a m2
  ok { a := m1, b := m3 }

/-- [aspis_core::field::{aspis_core::field::QM31}::ZERO]
    Source: 'crates/aspis-core/src/field.rs', lines 869:4-878:6
    Visibility: public -/
@[global_simps, irreducible]
def field.QM31.ZERO : field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

/-- [aspis_core::field::{aspis_core::field::QM31}::add]:
    Source: 'crates/aspis-core/src/field.rs', lines 896:4-903:5
    Visibility: public -/
def field.QM31.add
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let c ← field.CM31.add self.c0 rhs.c0
  let c1 ← field.CM31.add self.c1 rhs.c1
  ok { c0 := c, c1 }

/-- [aspis_core::field::{aspis_core::field::QM31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 935:4-945:5
    Visibility: public -/
def field.QM31.mul
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let m0 ← field.CM31.mul self.c0 rhs.c0
  let m1 ← field.CM31.mul self.c1 rhs.c1
  let c ← field.CM31.add self.c0 self.c1
  let c1 ← field.CM31.add rhs.c0 rhs.c1
  let m2 ← field.CM31.mul c c1
  let c2 ← field.mul_by_r m1
  let c3 ← field.CM31.add m0 c2
  let c4 ← field.CM31.sub m2 m0
  let c5 ← field.CM31.sub c4 m1
  ok { c0 := c3, c1 := c5 }

end PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs
end AspisR1SemanticCallExtraction

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.P : @AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.P = @AspisR1SemanticCallExtraction.aspis_core.field.P := by
  (trace "PRV-S2 PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.P"; delta AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.P AspisR1SemanticCallExtraction.aspis_core.field.P; try rfl; done)
#print axioms PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.P

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.reduce_u64 : @AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.reduce_u64 = @AspisR1SemanticCallExtraction.aspis_core.field.reduce_u64 := by
  (trace "PRV-S2 PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.reduce_u64"; delta AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.reduce_u64 AspisR1SemanticCallExtraction.aspis_core.field.reduce_u64; try simp only [PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.P]; try rfl; done)
#print axioms PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.reduce_u64

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.add : @AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.M31.add = @AspisR1SemanticCallExtraction.aspis_core.field.M31.add := by
  (trace "PRV-S2 PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.add"; delta AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.M31.add AspisR1SemanticCallExtraction.aspis_core.field.M31.add; try simp only [PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.P]; try rfl; done)
#print axioms PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.add

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.sub : @AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.M31.sub = @AspisR1SemanticCallExtraction.aspis_core.field.M31.sub := by
  (trace "PRV-S2 PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.sub"; delta AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.M31.sub AspisR1SemanticCallExtraction.aspis_core.field.M31.sub; try simp only [PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.P]; try rfl; done)
#print axioms PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.sub

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.mul : @AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.M31.mul = @AspisR1SemanticCallExtraction.aspis_core.field.M31.mul := by
  (trace "PRV-S2 PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.mul"; delta AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.M31.mul AspisR1SemanticCallExtraction.aspis_core.field.M31.mul; try simp only [PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.reduce_u64]; try rfl; done)
#print axioms PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.mul

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.reduce_u64 : @AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.M31.reduce_u64 = @AspisR1SemanticCallExtraction.aspis_core.field.M31.reduce_u64 := by
  (trace "PRV-S2 PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.reduce_u64"; delta AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.M31.reduce_u64 AspisR1SemanticCallExtraction.aspis_core.field.M31.reduce_u64; try simp only [PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.reduce_u64]; try rfl; done)
#print axioms PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.reduce_u64

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.double : @AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.M31.double = @AspisR1SemanticCallExtraction.aspis_core.field.M31.double := by
  (trace "PRV-S2 PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.double"; delta AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.M31.double AspisR1SemanticCallExtraction.aspis_core.field.M31.double; try simp only [PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.add]; try rfl; done)
#print axioms PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.double

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.CM31.add : @AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.CM31.add = @AspisR1SemanticCallExtraction.aspis_core.field.CM31.add := by
  (trace "PRV-S2 PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.CM31.add"; delta AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.CM31.add AspisR1SemanticCallExtraction.aspis_core.field.CM31.add; try simp only [PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.add]; try rfl; done)
#print axioms PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.CM31.add

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.CM31.sub : @AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.CM31.sub = @AspisR1SemanticCallExtraction.aspis_core.field.CM31.sub := by
  (trace "PRV-S2 PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.CM31.sub"; delta AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.CM31.sub AspisR1SemanticCallExtraction.aspis_core.field.CM31.sub; try simp only [PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.sub]; try rfl; done)
#print axioms PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.CM31.sub

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.CM31.mul : @AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.CM31.mul = @AspisR1SemanticCallExtraction.aspis_core.field.CM31.mul := by
  (trace "PRV-S2 PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.CM31.mul"; delta AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.CM31.mul AspisR1SemanticCallExtraction.aspis_core.field.CM31.mul; try simp only [PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.sub, PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.mul, PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.reduce_u64]; try rfl; done)
#print axioms PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.CM31.mul

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.mul_by_r : @AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.mul_by_r = @AspisR1SemanticCallExtraction.aspis_core.field.mul_by_r := by
  (trace "PRV-S2 PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.mul_by_r"; delta AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.mul_by_r AspisR1SemanticCallExtraction.aspis_core.field.mul_by_r; try simp only [PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.add, PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.sub, PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.M31.double]; try rfl; done)
#print axioms PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.mul_by_r

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.QM31.ZERO : @AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.QM31.ZERO = @AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO := by
  (trace "PRV-S2 PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.QM31.ZERO"; delta AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.QM31.ZERO AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO; try rfl; done)
#print axioms PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.QM31.ZERO

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.QM31.add : @AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.QM31.add = @AspisR1SemanticCallExtraction.aspis_core.field.QM31.add := by
  (trace "PRV-S2 PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.QM31.add"; delta AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.QM31.add AspisR1SemanticCallExtraction.aspis_core.field.QM31.add; try simp only [PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.CM31.add]; try rfl; done)
#print axioms PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.QM31.add

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.QM31.mul : @AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.QM31.mul = @AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul := by
  (trace "PRV-S2 PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.QM31.mul"; delta AspisR1SemanticCallExtraction.PRVFresh_C05_F17_AspisR1SemanticCallExtraction_Funs.field.QM31.mul AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul; try simp only [PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.CM31.add, PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.CM31.sub, PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.CM31.mul, PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.mul_by_r]; try rfl; done)
#print axioms PRVEq.C05_F17.AspisR1SemanticCallExtraction.Funs.field.QM31.mul


end
end PRVBundle_17
section PRVBundle_18
-- GENERATED by PCUF_gen_equalities.py for gate module AspisR1TerminalDecoder.Funs. Statements are against the gate constants of AspisR1TerminalDecoder.Funs.
-- fresh emission: PCQF_aspis_statement_pool_v1_payment_relation -> PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs; fresh source sha256 d6414d75b59fa3a3f0e3951977ec26429444796234f082319fb4a47796f186ba
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1TerminalDecoder
namespace PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs

/-- Trait implementation: [core::clone::impls::{impl core::clone::Clone for &'_0 T}]
    Source: '/rustc/library/core/src/clone.rs', lines 763:4-763:44
    Name pattern: [core::clone::Clone<&'0 @T>] -/
@[reducible]
def Shared0T.Insts.CoreCloneClone (T : Type) : core.clone.Clone T := {
  clone := core.clone.impls.CloneShared.clone
}

/-- Trait implementation: [core::marker::{impl core::marker::Copy for &'_0 T}]
    Source: '/rustc/library/core/src/marker.rs', lines 488:0-488:33
    Name pattern: [core::marker::Copy<&'0 @T>] -/
@[reducible]
def Shared0T.Insts.CoreMarkerCopy (T : Type) : core.marker.Copy T := {
  cloneInst := Shared0T.Insts.CoreCloneClone T
}

/-- [core::option::{core::option::Option<T>}::ok_or]:
    Source: '/rustc/library/core/src/option.rs', lines 1334:4-1334:73
    Name pattern: [core::option::{core::option::Option<@T>}::ok_or]
    Visibility: public -/
def core.option.Option.ok_or
  {T : Type} {E : Type} (self : Option T) (err : E) :
  Result (core.result.Result T E)
  := do
  match self with
  | none => ok (core.result.Result.Err err)
  | some v => ok (core.result.Result.Ok v)

/-- Trait implementation: [core::slice::cmp::{impl core::cmp::PartialEq<[U]> for [T]}]
    Source: '/rustc/library/core/src/slice/cmp.rs', lines 14:0-16:28
    Name pattern: [core::cmp::PartialEq<[@T], [@U]>] -/
@[reducible]
impl_def Slice.Insts.CoreCmpPartialEqSlice {T : Type} {U : Type}
  (cmpPartialEqInst : core.cmp.PartialEq T U) : core.cmp.PartialEq (Slice T)
  (Slice U) := {
  eq := core.slice.cmp.PartialEqSlice.eq cmpPartialEqInst
  ne := core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice
    cmpPartialEqInst)
}

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:16
    Name pattern: [aspis_core::field::P]
    Visibility: public -/
@[global_simps, irreducible]
def aspis_core.field.P : Std.U32 := 2147483647#u32

/-- [aspis_statement::atomic_statement::unwrap_fixed_slice]:
    Source: 'crates/aspis-statement/src/atomic_statement.rs', lines 84:0-89:1 -/
def atomic_statement.unwrap_fixed_slice
  {T : Type} (coremarkerCopyInst : core.marker.Copy T)
  (value : core.result.Result T core.array.TryFromSliceError) :
  Result T
  := do
  match value with
  | core.result.Result.Ok value1 => ok value1
  | core.result.Result.Err _ => fail panic

/-- [aspis_statement::atomic_statement::decode_digest_canonical]:
    Source: 'crates/aspis-statement/src/atomic_statement.rs', lines 91:0-110:1
    Visibility: public -/
def atomic_statement.decode_digest_canonical
  (bytes : Array Std.U8 32#usize) :
  Result (core.result.Result (Array aspis_core.field.M31 8#usize)
    atomic_statement.AtomicStatementError)
  := do
  let i ← Array.index_usize bytes 0#usize
  let i1 ← Array.index_usize bytes 1#usize
  let i2 ← Array.index_usize bytes 2#usize
  let i3 ← Array.index_usize bytes 3#usize
  let o ←
    aspis_core.field.M31.from_le_bytes (Array.make 4#usize [ i, i1, i2, i3 ])
  let r ←
    core.option.Option.ok_or o
      atomic_statement.AtomicStatementError.NonCanonicalDigest
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let i4 ← Array.index_usize bytes 4#usize
    let i5 ← Array.index_usize bytes 5#usize
    let i6 ← Array.index_usize bytes 6#usize
    let i7 ← Array.index_usize bytes 7#usize
    let o1 ←
      aspis_core.field.M31.from_le_bytes
        (Array.make 4#usize [ i4, i5, i6, i7 ])
    let r1 ←
      core.option.Option.ok_or o1
        atomic_statement.AtomicStatementError.NonCanonicalDigest
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let i8 ← Array.index_usize bytes 8#usize
      let i9 ← Array.index_usize bytes 9#usize
      let i10 ← Array.index_usize bytes 10#usize
      let i11 ← Array.index_usize bytes 11#usize
      let o2 ←
        aspis_core.field.M31.from_le_bytes
          (Array.make 4#usize [ i8, i9, i10, i11 ])
      let r2 ←
        core.option.Option.ok_or o2
          atomic_statement.AtomicStatementError.NonCanonicalDigest
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let i12 ← Array.index_usize bytes 12#usize
        let i13 ← Array.index_usize bytes 13#usize
        let i14 ← Array.index_usize bytes 14#usize
        let i15 ← Array.index_usize bytes 15#usize
        let o3 ←
          aspis_core.field.M31.from_le_bytes
            (Array.make 4#usize [ i12, i13, i14, i15 ])
        let r3 ←
          core.option.Option.ok_or o3
            atomic_statement.AtomicStatementError.NonCanonicalDigest
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let i16 ← Array.index_usize bytes 16#usize
          let i17 ← Array.index_usize bytes 17#usize
          let i18 ← Array.index_usize bytes 18#usize
          let i19 ← Array.index_usize bytes 19#usize
          let o4 ←
            aspis_core.field.M31.from_le_bytes
              (Array.make 4#usize [ i16, i17, i18, i19 ])
          let r4 ←
            core.option.Option.ok_or o4
              atomic_statement.AtomicStatementError.NonCanonicalDigest
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let i20 ← Array.index_usize bytes 20#usize
            let i21 ← Array.index_usize bytes 21#usize
            let i22 ← Array.index_usize bytes 22#usize
            let i23 ← Array.index_usize bytes 23#usize
            let o5 ←
              aspis_core.field.M31.from_le_bytes
                (Array.make 4#usize [ i20, i21, i22, i23 ])
            let r5 ←
              core.option.Option.ok_or o5
                atomic_statement.AtomicStatementError.NonCanonicalDigest
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val5 =>
              let i24 ← Array.index_usize bytes 24#usize
              let i25 ← Array.index_usize bytes 25#usize
              let i26 ← Array.index_usize bytes 26#usize
              let i27 ← Array.index_usize bytes 27#usize
              let o6 ←
                aspis_core.field.M31.from_le_bytes
                  (Array.make 4#usize [ i24, i25, i26, i27 ])
              let r6 ←
                core.option.Option.ok_or o6
                  atomic_statement.AtomicStatementError.NonCanonicalDigest
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue val6 =>
                let i28 ← Array.index_usize bytes 28#usize
                let i29 ← Array.index_usize bytes 29#usize
                let i30 ← Array.index_usize bytes 30#usize
                let i31 ← Array.index_usize bytes 31#usize
                let o7 ←
                  aspis_core.field.M31.from_le_bytes
                    (Array.make 4#usize [ i28, i29, i30, i31 ])
                let r7 ←
                  core.option.Option.ok_or o7
                    atomic_statement.AtomicStatementError.NonCanonicalDigest
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val7 =>
                  ok (core.result.Result.Ok
                    (Array.make 8#usize [
                      val, val1, val2, val3, val4, val5, val6, val7
                      ]))
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (Array aspis_core.field.M31 8#usize) (core.convert.FromSame
                    atomic_statement.AtomicStatementError) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (Array aspis_core.field.M31 8#usize) (core.convert.FromSame
                  atomic_statement.AtomicStatementError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (Array aspis_core.field.M31 8#usize) (core.convert.FromSame
                atomic_statement.AtomicStatementError) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (Array aspis_core.field.M31 8#usize) (core.convert.FromSame
              atomic_statement.AtomicStatementError) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (Array aspis_core.field.M31 8#usize) (core.convert.FromSame
            atomic_statement.AtomicStatementError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array aspis_core.field.M31 8#usize) (core.convert.FromSame
          atomic_statement.AtomicStatementError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array aspis_core.field.M31 8#usize) (core.convert.FromSame
        atomic_statement.AtomicStatementError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array aspis_core.field.M31 8#usize) (core.convert.FromSame
      atomic_statement.AtomicStatementError) residual

/-- [aspis_statement::pool_v1::format::POOL_V1_DIGEST_ENCODING_VERSION]
    Source: 'crates/aspis-statement/src/pool_v1/format.rs', lines 27:0-27:50
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION : Std.U8 := 1#u8

/-- [aspis_statement::pool_v1::format::POOL_V1_TREE_DEPTH]
    Source: 'crates/aspis-statement/src/pool_v1/format.rs', lines 28:0-28:41
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.format.POOL_V1_TREE_DEPTH : Std.Usize := 20#usize

/-- [aspis_statement::pool_v1::incremental_merkle::POOL_V1_LEAF_CAPACITY]
    Source: 'crates/aspis-statement/src/pool_v1/incremental_merkle.rs', lines 26:0-26:66
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY : Result Std.U64 :=
  1#u64 <<< pool_v1.format.POOL_V1_TREE_DEPTH

/-- [aspis_statement::pool_v1::payment_relation::POOL_V1_PAYMENT_STATEMENT_VERSION]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 29:0-29:52
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION : Std.U8 := 1#u8

/-- [aspis_statement::pool_v1::payment_relation::POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 30:0-30:71
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
  : Array Std.U8 4#usize :=
  Array.make 4#usize [ 65#u8, 83#u8, 67#u8, 80#u8 ]

/-- [aspis_statement::pool_v1::payment_relation::POOL_V1_WITHDRAWAL_STATEMENT_MAGIC]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 31:0-31:65
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC
  : Array Std.U8 4#usize :=
  Array.make 4#usize [ 65#u8, 83#u8, 87#u8, 80#u8 ]

/-- [aspis_statement::pool_v1::payment_relation::POOL_V1_CANONICAL_FEE]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 33:0-33:41
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.payment_relation.POOL_V1_CANONICAL_FEE : Std.U32 := 0#u32

/-- [aspis_statement::pool_v1::payment_relation::POOL_OFFSET]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 35:0-35:29 -/
@[global_simps, irreducible]
def pool_v1.payment_relation.POOL_OFFSET : Std.Usize := 8#usize

/-- [aspis_statement::pool_v1::payment_relation::DEPLOYMENT_DOMAIN_OFFSET]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 36:0-36:43 -/
@[global_simps, irreducible]
def pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET : Std.Usize := 40#usize

/-- [aspis_statement::pool_v1::payment_relation::ANCHOR_SEQUENCE_OFFSET]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 37:0-37:41 -/
@[global_simps, irreducible]
def pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET : Std.Usize := 72#usize

/-- [aspis_statement::pool_v1::payment_relation::ANCHOR_ROOT_OFFSET]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 38:0-38:37 -/
@[global_simps, irreducible]
def pool_v1.payment_relation.ANCHOR_ROOT_OFFSET : Std.Usize := 80#usize

/-- [aspis_statement::pool_v1::payment_relation::NULLIFIER_OFFSET]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 39:0-39:36 -/
@[global_simps, irreducible]
def pool_v1.payment_relation.NULLIFIER_OFFSET : Std.Usize := 112#usize

/-- [aspis_statement::pool_v1::payment_relation::ASSET_ID_OFFSET]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 40:0-40:35 -/
@[global_simps, irreducible]
def pool_v1.payment_relation.ASSET_ID_OFFSET : Std.Usize := 144#usize

/-- [aspis_statement::pool_v1::payment_relation::AMOUNT_OR_RESERVED_OFFSET]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 41:0-41:45 -/
@[global_simps, irreducible]
def pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET : Std.Usize := 148#usize

/-- [aspis_statement::pool_v1::payment_relation::FIRST_OUTPUT_OR_DESTINATION_OFFSET]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 42:0-42:54 -/
@[global_simps, irreducible]
def pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET : Std.Usize :=
  152#usize

/-- [aspis_statement::pool_v1::payment_relation::SECOND_OUTPUT_OFFSET]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 43:0-43:40 -/
@[global_simps, irreducible]
def pool_v1.payment_relation.SECOND_OUTPUT_OFFSET : Std.Usize := 184#usize

/-- [aspis_statement::pool_v1::payment_relation::digest_is_canonical]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 178:0-187:1 -/
def pool_v1.payment_relation.digest_is_canonical
  (digest : Array aspis_core.field.M31 8#usize) : Result Bool := do
  let m ← Array.index_usize digest 0#usize
  if m < aspis_core.field.P
  then
    let m1 ← Array.index_usize digest 1#usize
    if m1 < aspis_core.field.P
    then
      let m2 ← Array.index_usize digest 2#usize
      if m2 < aspis_core.field.P
      then
        let m3 ← Array.index_usize digest 3#usize
        if m3 < aspis_core.field.P
        then
          let m4 ← Array.index_usize digest 4#usize
          if m4 < aspis_core.field.P
          then
            let m5 ← Array.index_usize digest 5#usize
            if m5 < aspis_core.field.P
            then
              let m6 ← Array.index_usize digest 6#usize
              if m6 < aspis_core.field.P
              then
                let m7 ← Array.index_usize digest 7#usize
                ok (m7 < aspis_core.field.P)
              else ok false
            else ok false
          else ok false
        else ok false
      else ok false
    else ok false
  else ok false

/-- [aspis_statement::pool_v1::payment_relation::validate_common]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 189:0-203:1 -/
def pool_v1.payment_relation.validate_common
  (common : pool_v1.payment_relation.CommonPublicV1) :
  Result (core.result.Result Unit
    pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
  := do
  let a := Array.repeat 32#usize 0#u8
  let b ←
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 common.pool a
  if b
  then
    ok (core.result.Result.Err
      pool_v1.payment_relation.PoolV1PaymentStatementFormatError.ZeroRequiredBinding)
  else
    let a1 := Array.repeat 32#usize 0#u8
    let b1 ←
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
        common.deployment_domain a1
    if b1
    then
      ok (core.result.Result.Err
        pool_v1.payment_relation.PoolV1PaymentStatementFormatError.ZeroRequiredBinding)
    else
      let i ← pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY
      if common.anchor_sequence > i
      then
        ok (core.result.Result.Err
          pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidAnchorSequence)
      else
        let b2 ←
          pool_v1.payment_relation.digest_is_canonical common.anchor_root
        if b2
        then
          let b3 ←
            pool_v1.payment_relation.digest_is_canonical common.nullifier
          if b3
          then
            let i1 := common.asset_id
            if i1 >= aspis_core.field.P
            then
              ok (core.result.Result.Err
                pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalAssetId)
            else ok (core.result.Result.Ok ())
          else
            ok (core.result.Result.Err
              pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest)
        else
          ok (core.result.Result.Err
            pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest)

/-- [aspis_statement::pool_v1::payment_relation::transfer_common]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 205:0-214:1 -/
def pool_v1.payment_relation.transfer_common
  (public1 : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
  Result pool_v1.payment_relation.CommonPublicV1
  := do
  ok
    {
      pool := public1.pool,
      deployment_domain := public1.deployment_domain,
      anchor_sequence := public1.anchor_sequence,
      anchor_root := public1.anchor_root,
      nullifier := public1.nullifier,
      asset_id := public1.asset_id
    }

/-- [aspis_statement::pool_v1::payment_relation::withdrawal_common]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 216:0-225:1 -/
def pool_v1.payment_relation.withdrawal_common
  (public1 : pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
  Result pool_v1.payment_relation.CommonPublicV1
  := do
  ok
    {
      pool := public1.pool,
      deployment_domain := public1.deployment_domain,
      anchor_sequence := public1.anchor_sequence,
      anchor_root := public1.anchor_root,
      nullifier := public1.nullifier,
      asset_id := public1.asset_id
    }

/-- [aspis_statement::pool_v1::payment_relation::validate_pool_v1_private_transfer_public_v1]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 227:0-237:1
    Visibility: public -/
def pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1
  (public1 : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
  Result (core.result.Result Unit
    pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
  := do
  let cpv ← pool_v1.payment_relation.transfer_common public1
  let r ← pool_v1.payment_relation.validate_common cpv
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let b ←
      pool_v1.payment_relation.digest_is_canonical public1.recipient_commitment
    if b
    then
      let b1 ←
        pool_v1.payment_relation.digest_is_canonical public1.change_commitment
      if b1
      then ok (core.result.Result.Ok ())
      else
        ok (core.result.Result.Err
          pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest)
    else
      ok (core.result.Result.Err
        pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame
      pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual

/-- [aspis_statement::spend::VALUE_LIMIT]
    Source: 'crates/aspis-statement/src/spend.rs', lines 9:0-9:37
    Visibility: public -/
@[global_simps, irreducible]
def spend.VALUE_LIMIT : Result Std.U32 := 1#u32 <<< 30#i32

/-- [aspis_statement::pool_v1::payment_relation::validate_pool_v1_withdrawal_public_v1]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 239:0-253:1
    Visibility: public -/
def pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1
  (public1 : pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
  Result (core.result.Result Unit
    pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
  := do
  let cpv ← pool_v1.payment_relation.withdrawal_common public1
  let r ← pool_v1.payment_relation.validate_common cpv
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    if public1.amount = 0#u32
    then
      ok (core.result.Result.Err
        pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidWithdrawalAmount)
    else
      let i ← spend.VALUE_LIMIT
      if public1.amount >= i
      then
        ok (core.result.Result.Err
          pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidWithdrawalAmount)
      else
        let a := Array.repeat 32#usize 0#u8
        let b ←
          core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
            public1.destination_token_account a
        if b
        then
          ok (core.result.Result.Err
            pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidDestination)
        else
          let b1 ←
            pool_v1.payment_relation.digest_is_canonical
              public1.change_commitment
          if b1
          then ok (core.result.Result.Ok ())
          else
            ok (core.result.Result.Err
              pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame
      pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual

/-- [aspis_statement::pool_v1::payment_relation::encode_common]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 255:0-276:1 -/
def pool_v1.payment_relation.encode_common
  (output : Array Std.U8 216#usize) (magic : Array Std.U8 4#usize)
  (kind : pool_v1.historical_anchor.PoolV1TransitionKind)
  (common : pool_v1.payment_relation.CommonPublicV1) :
  Result (Array Std.U8 216#usize)
  := do
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) output
      { «end» := 4#usize }
  let s1 ← lift (Array.to_slice magic)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let output1 := index_mut_back s2
  let output2 ←
    Array.update output1 4#usize
      pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION
  let kind1 := read_discriminant kind
  let i ← lift (UScalar.cast .U8 kind1)
  let output3 ← Array.update output2 5#usize i
  let output4 ←
    Array.update output3 6#usize pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
  let (s3, index_mut_back1) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output4
      {
        start := pool_v1.payment_relation.POOL_OFFSET,
        «end» := pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET
      }
  let s4 ← lift (Array.to_slice common.pool)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let output5 := index_mut_back1 s5
  let (s6, index_mut_back2) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output5
      {
        start := pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
        «end» := pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET
      }
  let s7 ← lift (Array.to_slice common.deployment_domain)
  let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
  let output6 := index_mut_back2 s8
  let (s9, index_mut_back3) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output6
      {
        start := pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,
        «end» := pool_v1.payment_relation.ANCHOR_ROOT_OFFSET
      }
  let a ← lift (core.num.U64.to_le_bytes common.anchor_sequence)
  let s10 ← lift (Array.to_slice a)
  let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
  let output7 := index_mut_back3 s11
  let (s12, index_mut_back4) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output7
      {
        start := pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
        «end» := pool_v1.payment_relation.NULLIFIER_OFFSET
      }
  let a1 ← atomic_statement.encode_digest_canonical common.anchor_root
  let s13 ← lift (Array.to_slice a1)
  let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
  let output8 := index_mut_back4 s14
  let (s15, index_mut_back5) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output8
      {
        start := pool_v1.payment_relation.NULLIFIER_OFFSET,
        «end» := pool_v1.payment_relation.ASSET_ID_OFFSET
      }
  let a2 ← atomic_statement.encode_digest_canonical common.nullifier
  let s16 ← lift (Array.to_slice a2)
  let s17 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s15 s16
  let output9 := index_mut_back5 s17
  let (s18, index_mut_back6) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output9
      {
        start := pool_v1.payment_relation.ASSET_ID_OFFSET,
        «end» := pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET
      }
  let a3 ← aspis_core.field.M31.to_le_bytes common.asset_id
  let s19 ← lift (Array.to_slice a3)
  let s20 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s18 s19
  ok (index_mut_back6 s20)

/-- [aspis_statement::pool_v1::payment_relation::encode_pool_v1_private_transfer_public_v1]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 278:0-299:1
    Visibility: public -/
def pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1
  (public1 : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
  Result (core.result.Result (Array Std.U8 216#usize)
    pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
  := do
  let r ←
    pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1
      public1
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let output := Array.repeat 216#usize 0#u8
    let cpv ← pool_v1.payment_relation.transfer_common public1
    let output1 ←
      pool_v1.payment_relation.encode_common output
        pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
        pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer cpv
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output1
        {
          start := pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
          «end» := pool_v1.payment_relation.SECOND_OUTPUT_OFFSET
        }
    let a ←
      atomic_statement.encode_digest_canonical public1.recipient_commitment
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let output2 := index_mut_back s2
    let (s3, index_mut_back1) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) output2
        { start := pool_v1.payment_relation.SECOND_OUTPUT_OFFSET }
    let a1 ←
      atomic_statement.encode_digest_canonical public1.change_commitment
    let s4 ← lift (Array.to_slice a1)
    let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
    let output3 := index_mut_back1 s5
    ok (core.result.Result.Ok output3)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array Std.U8 216#usize) (core.convert.FromSame
      pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual

/-- [aspis_statement::pool_v1::payment_relation::encode_pool_v1_withdrawal_public_v1]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 301:0-319:1
    Visibility: public -/
def pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1
  (public1 : pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
  Result (core.result.Result (Array Std.U8 216#usize)
    pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
  := do
  let r ←
    pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 public1
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let output := Array.repeat 216#usize 0#u8
    let cpv ← pool_v1.payment_relation.withdrawal_common public1
    let output1 ←
      pool_v1.payment_relation.encode_common output
        pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC
        pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal cpv
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output1
        {
          start := pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
          «end» :=
            pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET
        }
    let a ← lift (core.num.U32.to_le_bytes public1.amount)
    let s1 ← lift (Array.to_slice a)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let output2 := index_mut_back s2
    let (s3, index_mut_back1) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output2
        {
          start := pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
          «end» := pool_v1.payment_relation.SECOND_OUTPUT_OFFSET
        }
    let s4 ← lift (Array.to_slice public1.destination_token_account)
    let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
    let output3 := index_mut_back1 s5
    let (s6, index_mut_back2) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) output3
        { start := pool_v1.payment_relation.SECOND_OUTPUT_OFFSET }
    let a1 ←
      atomic_statement.encode_digest_canonical public1.change_commitment
    let s7 ← lift (Array.to_slice a1)
    let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
    let output4 := index_mut_back2 s8
    ok (core.result.Result.Ok output4)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array Std.U8 216#usize) (core.convert.FromSame
      pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual

/-- [aspis_statement::pool_v1::payment_relation::require_header]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 321:0-342:1 -/
def pool_v1.payment_relation.require_header
  (bytes : Array Std.U8 216#usize) (magic : Array Std.U8 4#usize)
  (kind : pool_v1.historical_anchor.PoolV1TransitionKind) :
  Result (core.result.Result Unit
    pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
  := do
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) bytes
      { «end» := 4#usize }
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) magic
      { start := 0#usize, «end» := 4#usize }
  let b ←
    core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice
      core.cmp.PartialEqU8) s s1
  if b
  then
    ok (core.result.Result.Err
      pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongMagic)
  else
    let i ← Array.index_usize bytes 4#usize
    if i != pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION
    then
      ok (core.result.Result.Err
        pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongVersion)
    else
      let i1 ← Array.index_usize bytes 5#usize
      let kind1 := read_discriminant kind
      let i2 ← lift (UScalar.cast .U8 kind1)
      if i1 != i2
      then
        ok (core.result.Result.Err
          pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongTransitionKind)
      else
        let i3 ← Array.index_usize bytes 6#usize
        if i3 != pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
        then
          ok (core.result.Result.Err
            pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongDigestEncoding)
        else
          let i4 ← Array.index_usize bytes 7#usize
          if i4 != 0#u8
          then
            ok (core.result.Result.Err
              pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonZeroReserved)
          else ok (core.result.Result.Ok ())

/-- [aspis_statement::pool_v1::payment_relation::decode_common::{impl core::ops::function::FnOnce<(aspis_statement::atomic_statement::AtomicStatementError,), aspis_statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError> for aspis_statement::pool_v1::payment_relation::decode_common::closure#1}::call_once]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 370:17-370:74 -/
def
  pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once
  (c : pool_v1.payment_relation.decode_common.closure_1)
  (tupled_args : atomic_statement.AtomicStatementError) :
  Result pool_v1.payment_relation.PoolV1PaymentStatementFormatError
  := do
  ok
    pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest

/-- Trait implementation: [aspis_statement::pool_v1::payment_relation::decode_common::{impl core::ops::function::FnOnce<(aspis_statement::atomic_statement::AtomicStatementError,), aspis_statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError> for aspis_statement::pool_v1::payment_relation::decode_common::closure#1}]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 370:17-370:74 -/
@[reducible]
def
  pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError
  : core.ops.function.FnOnce pool_v1.payment_relation.decode_common.closure_1
  atomic_statement.AtomicStatementError
  pool_v1.payment_relation.PoolV1PaymentStatementFormatError := {
  call_once :=
    pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once
}

/-- [aspis_statement::pool_v1::payment_relation::decode_common::{impl core::ops::function::FnOnce<(aspis_statement::atomic_statement::AtomicStatementError,), aspis_statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError> for aspis_statement::pool_v1::payment_relation::decode_common::closure}::call_once]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 366:17-366:74 -/
def
  pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once
  (c : pool_v1.payment_relation.decode_common.closure)
  (tupled_args : atomic_statement.AtomicStatementError) :
  Result pool_v1.payment_relation.PoolV1PaymentStatementFormatError
  := do
  ok
    pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest

/-- Trait implementation: [aspis_statement::pool_v1::payment_relation::decode_common::{impl core::ops::function::FnOnce<(aspis_statement::atomic_statement::AtomicStatementError,), aspis_statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError> for aspis_statement::pool_v1::payment_relation::decode_common::closure}]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 366:17-366:74 -/
@[reducible]
def
  pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError
  : core.ops.function.FnOnce pool_v1.payment_relation.decode_common.closure
  atomic_statement.AtomicStatementError
  pool_v1.payment_relation.PoolV1PaymentStatementFormatError := {
  call_once :=
    pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once
}

/-- [aspis_statement::pool_v1::payment_relation::decode_common]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 344:0-375:1 -/
def pool_v1.payment_relation.decode_common
  (bytes : Array Std.U8 216#usize) :
  Result (core.result.Result pool_v1.payment_relation.CommonPublicV1
    pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
  := do
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes
      {
        start := pool_v1.payment_relation.ASSET_ID_OFFSET,
        «end» := pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET
      }
  let r ←
    core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s
  let a ←
    atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 4#usize
      core.marker.CopyU8) r
  let asset ← lift (core.num.U32.from_le_bytes a)
  if asset >= aspis_core.field.P
  then
    ok (core.result.Result.Err
      pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalAssetId)
  else
    let s1 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes
        {
          start := pool_v1.payment_relation.POOL_OFFSET,
          «end» := pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET
        }
    let r1 ←
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s1
    let a1 ←
      atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize
        core.marker.CopyU8) r1
    let s2 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes
        {
          start := pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
          «end» := pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET
        }
    let r2 ←
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s2
    let a2 ←
      atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize
        core.marker.CopyU8) r2
    let s3 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes
        {
          start := pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,
          «end» := pool_v1.payment_relation.ANCHOR_ROOT_OFFSET
        }
    let r3 ←
      core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s3
    let a3 ←
      atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 8#usize
        core.marker.CopyU8) r3
    let i ← lift (core.num.U64.from_le_bytes a3)
    let s4 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes
        {
          start := pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
          «end» := pool_v1.payment_relation.NULLIFIER_OFFSET
        }
    let r4 ← core.array.TryFromSharedArraySlice.try_from 32#usize s4
    let a4 ←
      atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array
        Std.U8 32#usize)) r4
    let r5 ← atomic_statement.decode_digest_canonical a4
    let r6 ←
      core.result.Result.map_err
        pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError
        r5 ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r6
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let s5 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes
          {
            start := pool_v1.payment_relation.NULLIFIER_OFFSET,
            «end» := pool_v1.payment_relation.ASSET_ID_OFFSET
          }
      let r7 ← core.array.TryFromSharedArraySlice.try_from 32#usize s5
      let a5 ←
        atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy
          (Array Std.U8 32#usize)) r7
      let r8 ← atomic_statement.decode_digest_canonical a5
      let r9 ←
        core.result.Result.map_err
          pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError
          r8 ()
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r9
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let r10 ←
          pool_v1.payment_relation.validate_common
            {
              pool := a1,
              deployment_domain := a2,
              anchor_sequence := i,
              anchor_root := val,
              nullifier := val1,
              asset_id := asset
            }
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r10
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (core.result.Result.Ok
            {
              pool := a1,
              deployment_domain := a2,
              anchor_sequence := i,
              anchor_root := val,
              nullifier := val1,
              asset_id := asset
            })
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            pool_v1.payment_relation.CommonPublicV1 (core.convert.FromSame
            pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          pool_v1.payment_relation.CommonPublicV1 (core.convert.FromSame
          pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        pool_v1.payment_relation.CommonPublicV1 (core.convert.FromSame
        pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual

/-- [aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1::{impl core::ops::function::FnOnce<(aspis_statement::atomic_statement::AtomicStatementError,), aspis_statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError> for aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1::closure#2}::call_once]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 408:17-408:74 -/
def
  pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once
  (c :
  pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2)
  (tupled_args : atomic_statement.AtomicStatementError) :
  Result pool_v1.payment_relation.PoolV1PaymentStatementFormatError
  := do
  ok
    pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest

/-- Trait implementation: [aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1::{impl core::ops::function::FnOnce<(aspis_statement::atomic_statement::AtomicStatementError,), aspis_statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError> for aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1::closure#2}]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 408:17-408:74 -/
@[reducible]
def
  pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError
  : core.ops.function.FnOnce
  pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2
  atomic_statement.AtomicStatementError
  pool_v1.payment_relation.PoolV1PaymentStatementFormatError := {
  call_once :=
    pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once
}

/-- [aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1::{impl core::ops::function::FnOnce<(aspis_statement::atomic_statement::AtomicStatementError,), aspis_statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError> for aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1::closure#1}::call_once]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 404:17-404:74 -/
def
  pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once
  (c :
  pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1)
  (tupled_args : atomic_statement.AtomicStatementError) :
  Result pool_v1.payment_relation.PoolV1PaymentStatementFormatError
  := do
  ok
    pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest

/-- Trait implementation: [aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1::{impl core::ops::function::FnOnce<(aspis_statement::atomic_statement::AtomicStatementError,), aspis_statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError> for aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1::closure#1}]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 404:17-404:74 -/
@[reducible]
def
  pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError
  : core.ops.function.FnOnce
  pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1
  atomic_statement.AtomicStatementError
  pool_v1.payment_relation.PoolV1PaymentStatementFormatError := {
  call_once :=
    pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once
}

/-- [aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1::{impl core::ops::function::FnOnce<(core::array::TryFromSliceError,), aspis_statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError> for aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1::closure}::call_once]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 382:17-382:67 -/
def
  pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once
  (c :
  pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure)
  (tupled_args : core.array.TryFromSliceError) :
  Result pool_v1.payment_relation.PoolV1PaymentStatementFormatError
  := do
  ok pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongLength

/-- Trait implementation: [aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1::{impl core::ops::function::FnOnce<(core::array::TryFromSliceError,), aspis_statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError> for aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1::closure}]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 382:17-382:67 -/
@[reducible]
def
  pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError
  : core.ops.function.FnOnce
  pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure
  core.array.TryFromSliceError
  pool_v1.payment_relation.PoolV1PaymentStatementFormatError := {
  call_once :=
    pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once
}

/-- [aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 377:0-412:1
    Visibility: public -/
def pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1
  (bytes : Slice Std.U8) :
  Result (core.result.Result
    pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
    pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
  := do
  let r ← core.array.TryFromSharedArraySlice.try_from 216#usize bytes
  let r1 ←
    core.result.Result.map_err
      pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r2 ←
      pool_v1.payment_relation.require_header val
        pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
        pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) val
          {
            start := pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
            «end» :=
              pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET
          }
      let a ←
        lift (core.num.U32.to_le_bytes
          pool_v1.payment_relation.POOL_V1_CANONICAL_FEE)
      let s1 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a
          { start := 0#usize, «end» := 4#usize }
      let b ←
        core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice
          core.cmp.PartialEqU8) s s1
      if b
      then
        ok (core.result.Result.Err
          pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonZeroReserved)
      else
        let r3 ← pool_v1.payment_relation.decode_common val
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let s2 ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) val
              {
                start :=
                  pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
                «end» := pool_v1.payment_relation.SECOND_OUTPUT_OFFSET
              }
          let r4 ← core.array.TryFromSharedArraySlice.try_from 32#usize s2
          let a1 ←
            atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy
              (Array Std.U8 32#usize)) r4
          let r5 ← atomic_statement.decode_digest_canonical a1
          let r6 ←
            core.result.Result.map_err
              pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError
              r5 ()
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r6
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let s3 ←
              core.array.Array.index (core.ops.index.IndexSlice
                (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) val
                { start := pool_v1.payment_relation.SECOND_OUTPUT_OFFSET }
            let r7 ← core.array.TryFromSharedArraySlice.try_from 32#usize s3
            let a2 ←
              atomic_statement.unwrap_fixed_slice
                (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r7
            let r8 ← atomic_statement.decode_digest_canonical a2
            let r9 ←
              core.result.Result.map_err
                pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError
                r8 ()
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r9
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let r10 ←
                pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1
                  {
                    pool := val1.pool,
                    deployment_domain := val1.deployment_domain,
                    anchor_sequence := val1.anchor_sequence,
                    anchor_root := val1.anchor_root,
                    nullifier := val1.nullifier,
                    asset_id := val1.asset_id,
                    recipient_commitment := val2,
                    change_commitment := val3
                  }
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r10
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                ok (core.result.Result.Ok
                  {
                    pool := val1.pool,
                    deployment_domain := val1.deployment_domain,
                    anchor_sequence := val1.anchor_sequence,
                    anchor_root := val1.anchor_root,
                    nullifier := val1.nullifier,
                    asset_id := val1.asset_id,
                    recipient_commitment := val2,
                    change_commitment := val3
                  })
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
                  (core.convert.FromSame
                  pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
                (core.convert.FromSame
                pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
              (core.convert.FromSame
              pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
            (core.convert.FromSame
            pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
            residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
        (core.convert.FromSame
        pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
      (core.convert.FromSame
      pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual

/-- [aspis_statement::pool_v1::payment_relation::decode_pool_v1_withdrawal_public_v1::{impl core::ops::function::FnOnce<(aspis_statement::atomic_statement::AtomicStatementError,), aspis_statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError> for aspis_statement::pool_v1::payment_relation::decode_pool_v1_withdrawal_public_v1::closure#1}::call_once]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 442:17-442:74 -/
def
  pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once
  (c : pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1)
  (tupled_args : atomic_statement.AtomicStatementError) :
  Result pool_v1.payment_relation.PoolV1PaymentStatementFormatError
  := do
  ok
    pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest

/-- Trait implementation: [aspis_statement::pool_v1::payment_relation::decode_pool_v1_withdrawal_public_v1::{impl core::ops::function::FnOnce<(aspis_statement::atomic_statement::AtomicStatementError,), aspis_statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError> for aspis_statement::pool_v1::payment_relation::decode_pool_v1_withdrawal_public_v1::closure#1}]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 442:17-442:74 -/
@[reducible]
def
  pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError
  : core.ops.function.FnOnce
  pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1
  atomic_statement.AtomicStatementError
  pool_v1.payment_relation.PoolV1PaymentStatementFormatError := {
  call_once :=
    pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once
}

/-- [aspis_statement::pool_v1::payment_relation::decode_pool_v1_withdrawal_public_v1::{impl core::ops::function::FnOnce<(core::array::TryFromSliceError,), aspis_statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError> for aspis_statement::pool_v1::payment_relation::decode_pool_v1_withdrawal_public_v1::closure}::call_once]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 419:17-419:67 -/
def
  pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once
  (c : pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure)
  (tupled_args : core.array.TryFromSliceError) :
  Result pool_v1.payment_relation.PoolV1PaymentStatementFormatError
  := do
  ok pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongLength

/-- Trait implementation: [aspis_statement::pool_v1::payment_relation::decode_pool_v1_withdrawal_public_v1::{impl core::ops::function::FnOnce<(core::array::TryFromSliceError,), aspis_statement::pool_v1::payment_relation::PoolV1PaymentStatementFormatError> for aspis_statement::pool_v1::payment_relation::decode_pool_v1_withdrawal_public_v1::closure}]
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 419:17-419:67 -/
@[reducible]
def
  pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError
  : core.ops.function.FnOnce
  pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure
  core.array.TryFromSliceError
  pool_v1.payment_relation.PoolV1PaymentStatementFormatError := {
  call_once :=
    pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once
}

/-- [aspis_statement::pool_v1::payment_relation::decode_pool_v1_withdrawal_public_v1]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_relation.rs', lines 414:0-446:1
    Visibility: public -/
def pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1
  (bytes : Slice Std.U8) :
  Result (core.result.Result pool_v1.payment_relation.PoolV1WithdrawalPublicV1
    pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
  := do
  let r ← core.array.TryFromSharedArraySlice.try_from 216#usize bytes
  let r1 ←
    core.result.Result.map_err
      pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r2 ←
      pool_v1.payment_relation.require_header val
        pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC
        pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let r3 ← pool_v1.payment_relation.decode_common val
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let s ←
          core.array.Array.index (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) val
            {
              start := pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
              «end» :=
                pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET
            }
        let r4 ←
          core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8
            s
        let a ←
          atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy
            4#usize core.marker.CopyU8) r4
        let i ← lift (core.num.U32.from_le_bytes a)
        let s1 ←
          core.array.Array.index (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) val
            {
              start :=
                pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
              «end» := pool_v1.payment_relation.SECOND_OUTPUT_OFFSET
            }
        let r5 ←
          core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
            s1
        let a1 ←
          atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy
            32#usize core.marker.CopyU8) r5
        let s2 ←
          core.array.Array.index (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) val
            { start := pool_v1.payment_relation.SECOND_OUTPUT_OFFSET }
        let r6 ← core.array.TryFromSharedArraySlice.try_from 32#usize s2
        let a2 ←
          atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy
            (Array Std.U8 32#usize)) r6
        let r7 ← atomic_statement.decode_digest_canonical a2
        let r8 ←
          core.result.Result.map_err
            pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError
            r7 ()
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r8
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r9 ←
            pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1
              {
                pool := val1.pool,
                deployment_domain := val1.deployment_domain,
                anchor_sequence := val1.anchor_sequence,
                anchor_root := val1.anchor_root,
                nullifier := val1.nullifier,
                asset_id := val1.asset_id,
                amount := i,
                destination_token_account := a1,
                change_commitment := val2
              }
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r9
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            ok (core.result.Result.Ok
              {
                pool := val1.pool,
                deployment_domain := val1.deployment_domain,
                anchor_sequence := val1.anchor_sequence,
                anchor_root := val1.anchor_root,
                nullifier := val1.nullifier,
                asset_id := val1.asset_id,
                amount := i,
                destination_token_account := a1,
                change_commitment := val2
              })
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              pool_v1.payment_relation.PoolV1WithdrawalPublicV1
              (core.convert.FromSame
              pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            pool_v1.payment_relation.PoolV1WithdrawalPublicV1
            (core.convert.FromSame
            pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          pool_v1.payment_relation.PoolV1WithdrawalPublicV1
          (core.convert.FromSame
          pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        pool_v1.payment_relation.PoolV1WithdrawalPublicV1
        (core.convert.FromSame
        pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      pool_v1.payment_relation.PoolV1WithdrawalPublicV1 (core.convert.FromSame
      pool_v1.payment_relation.PoolV1PaymentStatementFormatError) residual

end PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs
end AspisR1TerminalDecoder

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.Shared0T.Insts.CoreCloneClone : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.Shared0T.Insts.CoreCloneClone = @AspisR1TerminalDecoder.Shared0T.Insts.CoreCloneClone := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.Shared0T.Insts.CoreCloneClone"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.Shared0T.Insts.CoreCloneClone

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.Shared0T.Insts.CoreMarkerCopy : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.Shared0T.Insts.CoreMarkerCopy = @AspisR1TerminalDecoder.Shared0T.Insts.CoreMarkerCopy := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.Shared0T.Insts.CoreMarkerCopy"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.Shared0T.Insts.CoreMarkerCopy

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.core.option.Option.ok_or : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.core.option.Option.ok_or = @AspisR1TerminalDecoder.core.option.Option.ok_or := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.core.option.Option.ok_or"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.core.option.Option.ok_or

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.Slice.Insts.CoreCmpPartialEqSlice : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.Slice.Insts.CoreCmpPartialEqSlice = @AspisR1TerminalDecoder.Slice.Insts.CoreCmpPartialEqSlice := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.Slice.Insts.CoreCmpPartialEqSlice"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.Slice.Insts.CoreCmpPartialEqSlice

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.aspis_core.field.P : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.aspis_core.field.P = @AspisR1TerminalDecoder.aspis_core.field.P := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.aspis_core.field.P"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.aspis_core.field.P AspisR1TerminalDecoder.aspis_core.field.P; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.aspis_core.field.P

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.atomic_statement.unwrap_fixed_slice : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.atomic_statement.unwrap_fixed_slice = @AspisR1TerminalDecoder.atomic_statement.unwrap_fixed_slice := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.atomic_statement.unwrap_fixed_slice"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.atomic_statement.unwrap_fixed_slice

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.atomic_statement.decode_digest_canonical : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.atomic_statement.decode_digest_canonical = @AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.atomic_statement.decode_digest_canonical"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.atomic_statement.decode_digest_canonical

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION = @AspisR1TerminalDecoder.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION AspisR1TerminalDecoder.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.format.POOL_V1_TREE_DEPTH : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.format.POOL_V1_TREE_DEPTH = @AspisR1TerminalDecoder.pool_v1.format.POOL_V1_TREE_DEPTH := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.format.POOL_V1_TREE_DEPTH"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.format.POOL_V1_TREE_DEPTH AspisR1TerminalDecoder.pool_v1.format.POOL_V1_TREE_DEPTH; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.format.POOL_V1_TREE_DEPTH

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY = @AspisR1TerminalDecoder.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY AspisR1TerminalDecoder.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY; try simp only [PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.format.POOL_V1_TREE_DEPTH]; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION = @AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC = @AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC = @AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_CANONICAL_FEE : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.POOL_V1_CANONICAL_FEE = @AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_CANONICAL_FEE := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_CANONICAL_FEE"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.POOL_V1_CANONICAL_FEE AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_CANONICAL_FEE; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_CANONICAL_FEE

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_OFFSET : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.POOL_OFFSET = @AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_OFFSET := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_OFFSET"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.POOL_OFFSET AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_OFFSET; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_OFFSET

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET = @AspisR1TerminalDecoder.pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET AspisR1TerminalDecoder.pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET = @AspisR1TerminalDecoder.pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET AspisR1TerminalDecoder.pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.ANCHOR_ROOT_OFFSET : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.ANCHOR_ROOT_OFFSET = @AspisR1TerminalDecoder.pool_v1.payment_relation.ANCHOR_ROOT_OFFSET := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.ANCHOR_ROOT_OFFSET"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.ANCHOR_ROOT_OFFSET AspisR1TerminalDecoder.pool_v1.payment_relation.ANCHOR_ROOT_OFFSET; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.ANCHOR_ROOT_OFFSET

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.NULLIFIER_OFFSET : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.NULLIFIER_OFFSET = @AspisR1TerminalDecoder.pool_v1.payment_relation.NULLIFIER_OFFSET := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.NULLIFIER_OFFSET"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.NULLIFIER_OFFSET AspisR1TerminalDecoder.pool_v1.payment_relation.NULLIFIER_OFFSET; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.NULLIFIER_OFFSET

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.ASSET_ID_OFFSET : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.ASSET_ID_OFFSET = @AspisR1TerminalDecoder.pool_v1.payment_relation.ASSET_ID_OFFSET := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.ASSET_ID_OFFSET"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.ASSET_ID_OFFSET AspisR1TerminalDecoder.pool_v1.payment_relation.ASSET_ID_OFFSET; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.ASSET_ID_OFFSET

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET = @AspisR1TerminalDecoder.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET AspisR1TerminalDecoder.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET = @AspisR1TerminalDecoder.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET AspisR1TerminalDecoder.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET = @AspisR1TerminalDecoder.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET AspisR1TerminalDecoder.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.digest_is_canonical : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.digest_is_canonical = @AspisR1TerminalDecoder.pool_v1.payment_relation.digest_is_canonical := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.digest_is_canonical"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.digest_is_canonical AspisR1TerminalDecoder.pool_v1.payment_relation.digest_is_canonical; try simp only [PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.aspis_core.field.P]; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.digest_is_canonical

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.validate_common : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.validate_common = @AspisR1TerminalDecoder.pool_v1.payment_relation.validate_common := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.validate_common"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.validate_common AspisR1TerminalDecoder.pool_v1.payment_relation.validate_common; try simp only [PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.aspis_core.field.P, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.digest_is_canonical]; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.validate_common

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.transfer_common : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.transfer_common = @AspisR1TerminalDecoder.pool_v1.payment_relation.transfer_common := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.transfer_common"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.transfer_common

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.withdrawal_common : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.withdrawal_common = @AspisR1TerminalDecoder.pool_v1.payment_relation.withdrawal_common := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.withdrawal_common"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.withdrawal_common

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 = @AspisR1TerminalDecoder.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 AspisR1TerminalDecoder.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1; try simp only [PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.digest_is_canonical, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.validate_common, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.transfer_common]; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.spend.VALUE_LIMIT : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.spend.VALUE_LIMIT = @AspisR1TerminalDecoder.spend.VALUE_LIMIT := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.spend.VALUE_LIMIT"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.spend.VALUE_LIMIT AspisR1TerminalDecoder.spend.VALUE_LIMIT; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.spend.VALUE_LIMIT

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 = @AspisR1TerminalDecoder.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 AspisR1TerminalDecoder.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1; try simp only [PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.digest_is_canonical, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.validate_common, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.withdrawal_common, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.spend.VALUE_LIMIT]; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.encode_common : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.encode_common = @AspisR1TerminalDecoder.pool_v1.payment_relation.encode_common := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.encode_common"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.encode_common AspisR1TerminalDecoder.pool_v1.payment_relation.encode_common; try simp only [PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.ANCHOR_ROOT_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.NULLIFIER_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.ASSET_ID_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET]; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.encode_common

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 = @AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1; try simp only [PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.transfer_common, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.encode_common]; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 = @AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1; try simp only [PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.withdrawal_common, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.encode_common]; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.require_header : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.require_header = @AspisR1TerminalDecoder.pool_v1.payment_relation.require_header := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.require_header"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.require_header AspisR1TerminalDecoder.pool_v1.payment_relation.require_header; try simp only [PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.Slice.Insts.CoreCmpPartialEqSlice, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION]; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.require_header

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_common = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_common := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_common AspisR1TerminalDecoder.pool_v1.payment_relation.decode_common; try simp only [PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.Shared0T.Insts.CoreMarkerCopy, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.aspis_core.field.P, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.atomic_statement.unwrap_fixed_slice, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.atomic_statement.decode_digest_canonical, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.ANCHOR_ROOT_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.NULLIFIER_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.ASSET_ID_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.validate_common, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError]; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1 : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1 = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1 := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1 AspisR1TerminalDecoder.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1; try simp only [PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.Shared0T.Insts.CoreMarkerCopy, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.Slice.Insts.CoreCmpPartialEqSlice, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.atomic_statement.unwrap_fixed_slice, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.atomic_statement.decode_digest_canonical, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_CANONICAL_FEE, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.require_header, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError]; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError.call_once

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError := by
  (trace "PRV-S1 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError"; rfl)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError

set_option maxHeartbeats 200000 in
theorem PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 : @AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 = @AspisR1TerminalDecoder.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 := by
  (trace "PRV-S2 PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1"; delta AspisR1TerminalDecoder.PRVFresh_C05_F18_AspisR1TerminalDecoder_Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 AspisR1TerminalDecoder.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1; try simp only [PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.Shared0T.Insts.CoreMarkerCopy, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.atomic_statement.unwrap_fixed_slice, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.atomic_statement.decode_digest_canonical, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.require_header, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_common, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PaymentStatementFormatError, PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError]; try rfl; done)
#print axioms PRVEq.C05_F18.AspisR1TerminalDecoder.Funs.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1


end
end PRVBundle_18
