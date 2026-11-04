import Aeneas
set_option autoImplicit false
noncomputable section
namespace PV_STX_Code
open Aeneas Aeneas.Std

/-- Syntax for reached calls and source control flow. This is a substrate;
no constructor takes a completed world run or a fabricated event suffix. -/
inductive Code (Op : Type → Type 1) : Type → Type 1 where
  | result {A : Type} (r : Result A) : Code Op A
  | call {A : Type} (op : Op A) : Code Op A
  | seq {A B : Type} (first : Code Op A) (next : A → Code Op B) : Code Op B
  | loop {S A : Type} (body : S → Code Op (ControlFlow S A)) (s : S) : Code Op A

variable {Op : Type → Type 1} {A B : Type}
instance : Monad (Code Op) where
  pure a := .result (.ok a)
  bind := .seq

/-- The fixed-dictionary interpretation. State is deliberately absent HERE,
not from the operational interpreter. It is used only for no-regression. -/
def denote (fixed : {X : Type} → Op X → Result X) : {X : Type} → Code Op X → Result X
  | _, .result r => r
  | _, .call op => fixed op
  | _, .seq c k => Aeneas.Std.bind (denote fixed c) (fun a => denote fixed (k a))
  | _, .loop body s => Aeneas.Std.loop (fun t => denote fixed (body t)) s

/-- An explicit continuation stack survives every interpreter cutoff. -/
inductive Kont (Op : Type → Type 1) (A : Type) : Type → Type 1 where
  | done : Kont Op A A
  | seq {X Y : Type} (next : X → Code Op Y) (rest : Kont Op A Y) : Kont Op A X
  | loop {S X : Type} (body : S → Code Op (ControlFlow S X))
      (rest : Kont Op A X) : Kont Op A (ControlFlow S X)

structure Config (Op : Type → Type 1) (A : Type) : Type 1 where
  carrier : Type
  code : Code Op carrier
  kont : Kont Op A carrier

def start (c : Code Op A) : Config Op A := ⟨A,c,.done⟩

def continueWith : {X : Type} → Kont Op A X → X → Sum (Result A) (Config Op A)
  | _, .done, a => .inl (.ok a)
  | _, .seq k rest, x => .inr ⟨_,k x,rest⟩
  | _, .loop body rest, .done a => .inr ⟨_,.result (.ok a),rest⟩
  | _, .loop body rest, .cont s => .inr ⟨_,.loop body s,rest⟩

def kontDenote (fixed : {X : Type} → Op X → Result X) :
    {X : Type} → Kont Op A X → Result X → Result A
  | _, .done, r => r
  | _, .seq k rest, r => kontDenote fixed rest
      (Aeneas.Std.bind r (fun a => denote fixed (k a)))
  | _, .loop body rest, r => kontDenote fixed rest
      (Aeneas.Std.bind r (fun cf => match cf with
        | .done a => .ok a
        | .cont s => Aeneas.Std.loop (fun t => denote fixed (body t)) s))

def configDenote (fixed : {X : Type} → Op X → Result X) (c : Config Op A) : Result A :=
  kontDenote fixed c.kont (denote fixed c.code)

theorem start_denote (fixed : {X : Type} → Op X → Result X) (c : Code Op A) :
    configDenote fixed (start c) = denote fixed c := rfl

#print axioms start_denote
end PV_STX_Code
