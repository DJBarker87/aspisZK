import SameBodyOrdinary
namespace AspisV8Completion.SameBodyOrdinaryFixtures
open SameBodyOrdinary
def ops : Arithmetic Nat := ⟨0,1,fun x y => (x+y)%17,fun x y => (x+17-y%17)%17,
  fun x y => x*y%17,fun x => x*x%17,
  fun x => (List.range 17).find? (fun y => x*y%17 == 1)⟩
def w : SameBodyRelation.Word Nat := fun i => if i.val=271 then 1
  else if i.val=359 then 4 else if i.val=388 then 7 else 0
def atX := prepare ops w 3 2 ⟨1,0⟩ ⟨0,1⟩
def atY := prepare ops w 3 2 ⟨0,1⟩ ⟨0,16⟩
def tests : List (String × Bool) :=
  [("nonvacuous x-chord ordinary input",atX.isSome),
   ("repaired first row is multiplied by kappa",atX.map (·.uncorrectedClaim) == some 2),
   ("OOD x-interpolant endpoint0",atX.map (fun p => ops.add p.intercept (ops.mul p.slope 1)) == some 4),
   ("OOD x-interpolant endpoint1",atX.map (·.intercept) == some 7),
   ("equal-x circle pair chooses y",atY.map (·.useX) == some false),
   ("equal-x first endpoint",atY.map (fun p => ops.add p.intercept (ops.mul p.slope 1)) == some 4),
   ("equal-x second endpoint",atY.map (fun p => ops.add p.intercept (ops.mul p.slope 16)) == some 7),
   ("equal points keep inverse failure",(prepare ops w 3 2 ⟨1,0⟩ ⟨1,0⟩).isNone),
   ("ordinary scalar tracks inactive mutation",
     (prepare ops (fun i => if i.val=358 then 5 else w i) 3 2 ⟨1,0⟩ ⟨0,1⟩).map
       (·.uncorrectedClaim) == some 7),
   ("OOD output tracks mutation",
     (prepare ops (fun i => if i.val=359 then 5 else w i) 3 2 ⟨1,0⟩ ⟨0,1⟩).map
       (fun p => p.oodBatches 0) == some 5)]
def main : IO Unit := do
  for (name,ok) in tests do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
  if !(tests.all Prod.snd) then throw (IO.userError "ordinary model fixture failed")
end AspisV8Completion.SameBodyOrdinaryFixtures
def main := AspisV8Completion.SameBodyOrdinaryFixtures.main
