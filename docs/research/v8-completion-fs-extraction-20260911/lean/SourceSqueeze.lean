import CausalPrograms
set_option autoImplicit false
namespace AspisV8Completion.SourceSqueeze
open CausalPrograms

abbrev Block := Fin 32 → UInt8
def bytes (s : Block) : List UInt8 := List.ofFn s
def squeezeInput (s : Block) : List UInt8 := bytes s ++ [1]
def advanceInput (s : Block) : List UInt8 := bytes s ++ [2]

/-- Source-shaped chronological interpreter of Transcript::squeeze_block.
The second input contains the OLD state, not the first hash answer. -/
def program (s : Block) : Program (List UInt8) Block 2 :=
  .ask (squeezeInput s) (fun _ => .ask (advanceInput s) (fun _ => .stop))

def functional (hash : List UInt8 → Block) (s : Block) : Block × Block :=
  (hash (squeezeInput s), hash (advanceInput s))

def realisedCoins (hash : List UInt8 → Block) (s : Block) : Fin 2 → Block :=
  fun i => if i.val = 0 then hash (squeezeInput s) else hash (advanceInput s)

theorem realised_execution (hash : List UInt8 → Block) (s : Block) :
    execute (program s) (realisedCoins hash s) =
      [(squeezeInput s, (functional hash s).1),
       (advanceInput s, (functional hash s).2)] := by
  rfl

/-- Every continuation preserves both requested byte strings. The answer to
the first hash does not retrospectively choose the advance input. -/
theorem requests_fixed (s : Block) (coins : Fin 2 → Block) :
    (execute (program s) coins).map Prod.fst = [squeezeInput s, advanceInput s] := by
  rfl

/-- Full hash answers remain available in the trace; no 208-bit truncation. -/
theorem answers_preserved (s : Block) (coins : Fin 2 → Block) :
    (execute (program s) coins).map Prod.snd = [coins 0, coins 1] := by
  rfl

theorem input_domains_distinct (s t : Block) : squeezeInput s ≠ advanceInput t := by
  intro h
  have last := congrArg List.getLast? h
  simp [squeezeInput, advanceInput] at last

/-- Restoring a state under the SAME oracle repeats answers. This is not
independent sampling and supplies no adversary retry discount. -/
theorem restore_same_oracle (hash : List UInt8 → Block) (s t : Block) (h : s = t) :
    execute (program s) (realisedCoins hash s) =
      execute (program t) (realisedCoins hash t) := by
  subst t
  rfl

#print realised_execution
#print requests_fixed
#print axioms realised_execution
#print axioms requests_fixed
#print axioms answers_preserved
#print axioms input_domains_distinct
#print axioms restore_same_oracle
end AspisV8Completion.SourceSqueeze
