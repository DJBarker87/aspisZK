import Lean
open Lean
partial def walk (par : IO.Ref (Std.HashMap Name Name)) (seen : IO.Ref (Std.HashSet Name)) (m p : Name) : IO Unit := do
  if (← seen.get).contains m then return
  seen.modify (·.insert m)
  par.modify (·.insert m p)
  let f ← findOLean m
  let (d, _) ← readModuleData f
  for i in d.imports do walk par seen i.module m
partial def chain (par : Std.HashMap Name Name) (m : Name) (acc : List Name) (fuel : Nat) : List Name :=
  match fuel with
  | 0 => acc
  | n+1 => match par.get? m with
    | some p => if p == m || p == Name.anonymous then m :: acc else chain par p (m :: acc) n
    | none => m :: acc
#eval show IO Unit from do
  let par ← IO.mkRef ({} : Std.HashMap Name Name)
  let seen ← IO.mkRef ({} : Std.HashSet Name)
  walk par seen `DrvI_Installation `DrvI_Installation
  let p ← par.get
  IO.println s!"n_modules {(← seen.get).size}"
  for t in [`S1SemanticPhaseV1, `AspisR1PublicPreparation.Types] do
    IO.println s!"{t}: {(chain p t [] 400)}"
