import SameBodyRelation
namespace AspisV8Completion.SameBodyRelationFixtures
open AspisV8Completion.SameBodyRelation

def ops : Arithmetic Nat := ⟨fun x y => (x+17-y%17)%17,
  fun x => x*13%17, fun p a => (List.finRange 7).reverse.foldl (fun x i => (x*a+p i)%17) 0⟩
def msg (x : Nat) : Sent Nat := fun i => (x+i.val)%17
def strategy : Strategy Nat Nat := fun tau =>
  ⟨msg tau, fun alpha => ⟨fun i => (tau+alpha+i.val)%17, fun q rho =>
    .round (msg (tau+alpha+q+rho)) (fun a1 =>
      .round (msg (a1+q)) (fun a2 => .round (msg (a1+a2+rho)) (fun _ => .done)))⟩⟩
def coins : Fin 3 → Nat := fun i => if i.val=0 then 3 else if i.val=1 then 5 else 7
def finals : Final Nat := ((strategy 2).afterAlpha0 4).final256
def rounds : Fin 4 → Sent Nat := fun i => if i.val=0 then msg 2 else if i.val=1 then msg 25
  else if i.val=2 then msg 9 else msg 21
def word : Word Nat := assemble (fun _ => 0) rounds finals
def run (w : Word Nat) := consume ops strategy w 2 4 6 13 coins 9 (fun _ _ _ => 2)
def tests : List (String × Bool) :=
  [("adaptive causal trace has a nonvacuous serialized run", (run word).isSome),
   ("changed response0 fails stale trace consistency", (run (fun i => if i.val=417 then 8 else word i)).isNone),
   ("changed final fails stale trace consistency", (run (fun i => if i.val=441 then 8 else word i)).isNone),
   ("changed late response fails stale trace consistency", (run (fun i => if i.val=435 then 8 else word i)).isNone),
   ("unconsumed semantic field intentionally not checked here", (run (fun i => if i.val=0 then 8 else word i)).isSome)]
def main : IO Unit := do
  for (name, passed) in tests do
    IO.println s!"{if passed then "PASS" else "FAIL"}: {name}"
  if !(tests.all Prod.snd) then throw (IO.userError "causal trace fixture failed")
end AspisV8Completion.SameBodyRelationFixtures
def main := AspisV8Completion.SameBodyRelationFixtures.main
