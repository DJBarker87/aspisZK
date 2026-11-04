import PV_STX_Code
set_option autoImplicit false
noncomputable section
namespace PV_STX_Map
open Aeneas Aeneas.Std PV_STX_Code
variable {Op Op' : Type → Type 1} {A : Type}

def map (inject : {X : Type} → Op X → Op' X) : {X : Type} → Code Op X → Code Op' X
  | _, .result r => .result r
  | _, .call op => .call (inject op)
  | _, .seq first next => .seq (map inject first) (fun a => map inject (next a))
  | _, .loop body s => .loop (fun t => map inject (body t)) s

/-- Modules inject primitive requests into ONE surrounding request family.
No nested world evaluator, per-module initial world, or fixed callback record
is installed by this operation. -/
theorem denote_map (inject : {X : Type} → Op X → Op' X)
    (fixed : {X : Type} → Op X → Result X)
    (fixed' : {X : Type} → Op' X → Result X)
    (same : ∀ {X : Type} (op : Op X), fixed' (inject op) = fixed op)
    (code : Code Op A) : denote fixed' (map inject code) = denote fixed code := by
  induction code with
  | result r => rfl
  | call op => exact same op
  | seq first next ihfirst ihnext =>
    simp only [map,denote,ihfirst]
    congr 1
    funext a
    exact ihnext a
  | loop body s ih =>
    change Aeneas.Std.loop (fun t => denote fixed' (map inject (body t))) s =
      Aeneas.Std.loop (fun t => denote fixed (body t)) s
    congr 1
    funext t
    exact ih t

#print axioms denote_map
end PV_STX_Map
