import SequentialProgramInvariants

namespace AspisR1.RRProgramTraversal
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Short-circuiting bind preserves an explicit abort. -/
def optionBind {I A X Y : Type} (p : Program I A (Option X))
    (next : X → Program I A (Option Y)) : Program I A (Option Y) :=
  bind p (fun out => match out with
    | none => .done none | some x => next x)

/-- Deterministic output mapping, preserving aborts. -/
def mapOption {I A X Y : Type} (p : Program I A (Option X)) (f : X → Y) :
    Program I A (Option Y) := bind p (fun out => .done (out.map f))

/-- Execute all reached child traversals in order and concatenate their
coefficient-prefix candidates. Any child abort aborts the whole traversal. -/
def walkChildren {I A K S : Type}
    (run : S → Program I A (Option (List (List K)))) :
    List (K × S) → Program I A (Option (List (List K)))
  | [] => .done (some [])
  | (a,s)::tail => optionBind (run s) (fun ys =>
      mapOption (walkChildren run tail) (fun zs => ys.map (a :: ·) ++ zs))

/-- The bounded RR prefix traversal with randomized child/root enumeration.
This program keeps every reached abort explicit and never uses an empty list
as a substitute for a failed root-finding call. -/
def collectProgram {I A K S : Type} (zeroTest : S → Bool)
    (children : S → Program I A (Option (List (K × S)))) :
    Nat → S → Program I A (Option (List (List K)))
  | 0, s => .done (some (if zeroTest s then [[]] else []))
  | d+1, s => optionBind (children s) (walkChildren (collectProgram zeroTest children d))

#print axioms optionBind
#print axioms mapOption
#print axioms walkChildren
#print axioms collectProgram
end AspisR1.RRProgramTraversal
