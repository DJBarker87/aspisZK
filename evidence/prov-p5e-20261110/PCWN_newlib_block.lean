/-! PCWN item X: the new (second tool version) Aeneas Lean library definitions, copied verbatim from
    src/aeneas/backends/lean/Aeneas/Std/Core/Convert.lean (Result.branch, Result.from_residual) and Std/Primitives.lean (Never);
    Aeneas 0d21a9ec7bbbb110110cacc14464a47fd71c8705, Convert.lean sha256 e258655835a72b3927bd2e2fb222467329b630d31f643ae26065be32ae6096ed,
    host path /home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/src/aeneas/backends/lean/Aeneas/Std/Core/Convert.lean.
    Only the attribute lists (@[expose, rust_fun ...]) are omitted; they do not change the definitions. -/
namespace PCWN_NewLib
open Aeneas.Std
/-- The Never type in Rust -/
inductive Never where

def core.result.Result.Insts.CoreOpsTry.branch
  {T E : Type _} :
  core.result.Result T E →
    Std.Result (core.ops.control_flow.ControlFlow
      (core.result.Result Never E) T)
  | .Ok v => .ok (.Continue v)
  | .Err e => .ok (.Break (.Err e))

def core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
  (T : Type _) {E F : Type _} (convertFromInst : core.convert.From F E)
  (r : core.result.Result Never E) : Std.Result (core.result.Result T F) :=
  match r with
  | .Ok x => x.casesOn
  | .Err e => do
      let v ← convertFromInst.from e
      .ok (.Err v)

/-- transport of the empty type: gate Infallible -> new Never -/
def castN (x : core.convert.Infallible) : PCWN_NewLib.Never := x.casesOn
def castR {E : Type} : core.result.Result core.convert.Infallible E → core.result.Result PCWN_NewLib.Never E
  | .Ok x => .Ok (castN x)
  | .Err e => .Err e

set_option maxHeartbeats 200000 in
/-- ITEM: new-library from_residual = gate-library from_residual, transported along the empty-type map. -/
theorem from_residual_eq (T : Type) {E F : Type} (inst : core.convert.From F E)
    (r : core.result.Result core.convert.Infallible E) :
    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T inst (castR r)
      = Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual T inst r := by
  cases r with
  | Ok x => exact x.casesOn
  | Err e => rfl
#print axioms from_residual_eq

set_option maxHeartbeats 200000 in
/-- branch bind-transport: Continue arms agree, Break arms agree on the transported residual (used by pb_chain). -/
theorem branch_bind {T E A : Type} (r : core.result.Result T E)
    (F : core.ops.control_flow.ControlFlow (core.result.Result PCWN_NewLib.Never E) T → Result A)
    (G : core.ops.control_flow.ControlFlow (core.result.Result core.convert.Infallible E) T → Result A)
    (hOk : ∀ v, F (.Continue v) = G (.Continue v)) (hErr : ∀ e, F (.Break (.Err e)) = G (.Break (.Err e))) :
    Bind.bind (PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch r) F
      = Bind.bind (Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch r) G := by
  cases r with
  | Ok v => exact hOk v
  | Err e => exact hErr e
#print axioms branch_bind
end PCWN_NewLib

macro "pb_chain" : tactic => `(tactic| (
  (try (refine funext fun _ => ?_; try refine funext fun _ => ?_))
  try dsimp only
  repeat' first
  | (refine PCWN_NewLib.branch_bind _ _ _ (fun v => ?_) (fun e => rfl); try dsimp only)
  | (refine congrArg (Bind.bind _) (funext fun x => ?_); try (obtain ⟨_, _⟩ := x); try dsimp only)
  | (split <;> (try simp only [*]))
  | exact rfl))
