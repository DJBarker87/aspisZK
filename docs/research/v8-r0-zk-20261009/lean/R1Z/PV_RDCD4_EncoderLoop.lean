import R1Z.PV_RDCD4_Chunks194
import R1Z.PV_RDCD4_ArraySuffix
import R1Z.PV_RDCD4_Zip194
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDCD4_EncoderLoop
set_option autoImplicit false

abbrev Iter (E : Type) :=
  PV_RDCD4_Zip194.State (PV_RDCD4_Chunks194.State E) (PV_RDCD4_ArrayIter194.State E)

def next {E : Type} (s : Iter E) :=
  PV_RDCD4_Zip194.next PV_RDCD4_Chunks194.next PV_RDCD4_ArrayIter194.next s

/-- A rank-bounded interpretation of the source for loop. The final None
inspection uses one rank unit. The fuel-zero branch is proved unreachable. -/
def loop {E S : Type} (step : (List E × E) → S → Result S) :
    Nat → Iter E → S → Result S
  | 0,_,_ => fail .panic
  | fuel+1,s,acc =>
    let (entry,s) := next s
    match entry with
    | none => ok acc
    | some e => do
      let acc ← step e acc
      loop step fuel s acc

def pairs {E : Type} : List E → List (List E)
  | a::b::tail => [a,b]::pairs tail
  | _ => []

def run {E S : Type} (step : (List E × E) → S → Result S) :
    List (List E × E) → S → Result S
  | [],acc => ok acc
  | e::tail,acc => do
    let acc ← step e acc
    run step tail acc

theorem done {E S : Type} (step : (List E × E) → S → Result S)
    (s : Iter E) (fuel : Nat) (acc : S) (h : (next s).1=none) :
    loop step (fuel+1) s acc=ok acc := by
  cases hn : next s with
  | mk entry rest =>
    have he : entry=none := by simpa only [hn] using h
    rw [loop,hn,he]

theorem advance {E S : Type} (step : (List E × E) → S → Result S)
    (s s' : Iter E) (e : List E × E) (fuel : Nat) (acc : S)
    (h : next s=(some e,s')) :
    loop step (fuel+1) s acc=(do
      let acc ← step e acc
      loop step fuel s' acc) := by
  rw [loop,h]

#print axioms done
#print axioms advance
end R1Z.PV_RDCD4_EncoderLoop
