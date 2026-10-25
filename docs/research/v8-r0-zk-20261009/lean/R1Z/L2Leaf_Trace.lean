import Std

/-! Executable source-observation REFERENCES. These are not extracted Rust.
Every event carries a static site and a dynamic value. Arithmetic operands
are a conservative observation for variable-latency operations; actual CPU
latency remains L3. No witness carrier is an input to these references.
Std/allocator/hash internals are NOT modeled by a single collection event. -/
set_option autoImplicit false
namespace R1Z.L2Leaf_Trace

inductive Event where
  | branch (site : String) (taken : Bool)
  | index (site : String) (index : Nat)
  | loop (site : String) (iteration : Nat)
  | alloc (site : String) (elements width : Nat)
  | collection (site : String) (operation : String) (size : Nat)
  | variableOp (site : String) (operation : String) (operands : List Nat)
  deriving DecidableEq, Repr
abbrev Trace := List Event

def branch (site : String) (b : Bool) : Trace := [.branch site b]

/-- Logical scalar equality, with limb-by-limb short-circuit semantics.
Rust's compiled slice equality is a separate refinement obligation. -/
def zeroTrace : Nat → List Nat → Bool × Trace
  | _, [] => (true, [])
  | i, x :: xs =>
    let hit := x == 0
    let head := [.index "zero" i, .branch "zero.eq" hit]
    if hit then
      let rest := zeroTrace (i+1) xs
      (rest.1, head ++ rest.2)
    else (false, head)

def twoSeedTrace (left right : List Nat) : Bool × Trace :=
  let a := zeroTrace 0 left
  if a.1 then (false, a.2 ++ branch "seed.and" false)
  else
    let b := zeroTrace 0 right
    (!b.1, a.2 ++ branch "seed.and" true ++ b.2)

structure Cursor where
  word : Nat
  counter : Nat
  deriving DecidableEq, Repr

/-- next_word addressing/refill, with the hash contents supplied by the raw
word source. Counter wrap is modulo 2^64, as in the Rust implementation. -/
def nextTrace (s : Cursor) : Cursor × Trace :=
  let refill := s.word == 8
  let word := if refill then 0 else s.word
  let counter := if refill then (s.counter+1) % (2^64) else s.counter
  (⟨word+1,counter⟩,
    branch "next.refill" refill ++
    (if refill then [.variableOp "next.hash" "hash" [s.counter]] else []) ++
    [.index "next.byte.start" (4*word), .index "next.byte.end" (4*word+4)])

/-- One of the identical 16-candidate m31 loops. The raw source includes
rejected words, not merely the successful field result. -/
def rejectionTrace (words : Nat → Nat) : Nat → Nat → Cursor → Option Nat × Cursor × Trace
  | 0, _, s => (none,s,branch "m31.exhausted" true)
  | fuel+1, draw, s =>
    let step := nextTrace s
    let candidate := words draw % (2^31)
    let accepted := candidate < 2147483647
    let head := [.loop "m31" draw] ++ step.2 ++ branch "m31.accept" accepted
    if accepted then (some candidate,step.1,head)
    else
      let rest := rejectionTrace words fuel (draw+1) step.1
      (rest.1,rest.2.1,head ++ rest.2.2)

def m31Trace (words : Nat → Nat) (s : Cursor) := rejectionTrace words 16 0 s

/-- Division pass: retained quotient writeback and /,% operands, not just
constant loop lengths. Input words must be canonical u32 for source use. -/
def divPass (words : List Nat) (remainder : Nat := 0) (index : Nat := 8) :
    List Nat × Nat × Trace :=
  match words with
  | [] => ([],remainder,[])
  | x::xs =>
    let dividend := remainder * (2^32) + x
    let rest := divPass xs (dividend % 2147483647) (index-1)
    ((dividend / 2147483647)::rest.1, rest.2.1,
      [.loop "div" (index-1), .index "rank" (index-1),
       .variableOp "div" "/%" [dividend,2147483647]] ++ rest.2.2)

def divisionTrace (passes : Nat) (rank : List Nat) : Trace :=
  match passes with
  | 0 => []
  | n+1 => let step := divPass rank; step.2.2 ++ divisionTrace n step.1

def addSmall (digits : List Nat) (carry : Nat) (i : Nat := 0) : List Nat × Nat × Trace :=
  match digits with
  | [] => ([],carry,[])
  | d::ds =>
    let sum := d+carry
    let rest := addSmall ds (sum / 2147483647) (i+1)
    ((sum % 2147483647)::rest.1, rest.2.1,
      [.loop "gamma.add" i,.index "gamma.digit" i,
       .variableOp "gamma.add" "/%" [sum,2147483647]] ++ rest.2.2)

def gammaCarryTrace (digits : List Nat) (quotient : Nat) : Trace :=
  let first := addSmall digits (quotient+1)
  let wrap := first.2.1 != 0
  first.2.2 ++ branch "gamma.wrap" wrap ++
    (if wrap then (addSmall first.1 1).2.2 else [])

/-- A supplied circle implementation must return its FULL arithmetic trace,
including inverse/subfield decisions. This interface does not discharge it. -/
def circleTrace (circle : List Nat → Bool × Trace) (rank : List Nat) (row : Nat) : Trace :=
  let result := circle rank
  divisionTrace 4 rank ++ result.2 ++ branch "circle.fallback" (!result.1) ++
    (if result.1 then [] else [.index "circle.fallback.row" row])

/-- Coordinates store full canonical limbs; equality short-circuits. -/
abbrev Coordinate := List Nat

def trailing (one : Coordinate) : List Coordinate → Nat × Trace
  | [] => (0,[])
  | x::xs =>
    let z := zeroTrace 0 x
    let isOne := x == one
    let tested := z.2 ++ (if z.1 then [] else branch "suffix.one" isOne)
    if z.1 || isOne then
      let rest := trailing one xs
      (rest.1+1,tested ++ branch "suffix.continue" true ++ rest.2)
    else (0,tested ++ branch "suffix.continue" false)

def sparseTrace (one : Coordinate) (point : List Coordinate) : Trace :=
  let t := trailing one point.reverse
  let prefixLen := point.length-t.1
  let suffix := (point.drop prefixLen).foldl (fun a x => 2*a + if x == one then 1 else 0) 0
  t.2 ++ [.alloc "sparse.weights" (2^prefixLen) 1, .loop "suffix" t.1] ++
    (List.range (2^prefixLen)).flatMap (fun p =>
      [.loop "sparse.prefix" p,.index "column.row" (p*(2^t.1)+suffix),
       .collection "weights" "push" p] ++
      (List.range prefixLen).flatMap (fun j =>
        [.loop "sparse.coordinate" j,.index "point" j,
         .branch "sparse.bit" ((p / (2^(prefixLen-1-j))) % 2 == 0)]))

/-- Exact duplicate-search positions for the scalar logical contains model. -/
def containsTrace (candidate : Nat) : Nat → List Nat → Bool × Trace
  | _, [] => (false,[])
  | i,x::xs =>
    let hit := x == candidate
    let head := [.index "accepted" i,.branch "contains.eq" hit]
    if hit then (true,head)
    else let rest := containsTrace candidate (i+1) xs; (rest.1,head ++ rest.2)

structure Scan where
  accepted : List Nat
  draws : Nat
  deriving DecidableEq, Repr

/-- One eight-word block, including the guard before each word and no guard
following the eighth. Block squeeze/advance occurs outside this function. -/
def queryBlockTrace : List Nat → Scan → Bool × Scan × Trace
  | [],s => (false,s,[])
  | x::xs,s =>
    let done := s.accepted.length == 22 || s.draws == 64
    if done then (true,s,branch "scan.done" true)
    else
      let found := containsTrace x 0 s.accepted
      let after : Scan := ⟨if found.1 then s.accepted else s.accepted ++ [x],s.draws+1⟩
      let rest := queryBlockTrace xs after
      (rest.1,rest.2.1,branch "scan.done" false ++ [.loop "scan" s.draws] ++ found.2 ++
        branch "scan.insert" (!found.1) ++
        (if found.1 then [] else [.index "accepted.write" s.accepted.length]) ++ rest.2.2)

/-- Shared binary sibling traversal for sorted unique indices. Validation,
node_count, sorting and allocation implementation costs are separate. -/
def siblingLevel : List Nat → List Nat × Trace
  | [] => ([],[])
  | x::xs =>
    let shared := xs.head? == some (x+1) && x % 2 == 0
    let remaining := if shared then xs.drop 1 else xs
    let rest := siblingLevel remaining
    ((x/2)::rest.1,
      [.index "query" x,.branch "sibling.shared" shared] ++
      (if shared then [] else [.index "tree.node" (if x % 2 == 0 then x+1 else x-1)]) ++
      [.collection "parents" "push" (x/2)] ++ rest.2)
termination_by indices => indices.length
decreasing_by
  simp_wf
  split <;> simp_all <;> omega

def multiproofTrace : Nat → List Nat → Trace
  | 0,_ => []
  | depth+1,indices =>
    let level := siblingLevel indices
    [.loop "multiproof.levels.remaining" (depth+1),.alloc "parents.initial" 0 4] ++
      level.2 ++ multiproofTrace depth level.1

/-- A concrete P_R1 small-step source semantics must provide this transition
on the entire checker/emitter state. The parameter is an OPEN refinement,
not a certified checker or an assumed witness-free cost oracle. -/
def checkerTrace {State : Type} (step : State → Option (Trace × State)) : Nat → State → Trace
  | 0,_ => []
  | fuel+1,s => match step s with
    | none => []
    | some (events,after) => events ++ checkerTrace step fuel after

/-- Sufficient equality is equality of ALL trace inputs. Equality only of
sampler outputs, final queries, checker bits or proof bytes is insufficient. -/
theorem trace_congr {Input : Type} (observe : Input → Trace) (a b : Input)
    (inputs : a = b) : observe a = observe b := congrArg observe inputs

/-- Successful nonzero tests can visit different bytes. The L1 seed-pair
permutation proof therefore cannot simply be relabeled an L2 trace proof. -/
theorem nonzero_verdict_not_trace :
    (twoSeedTrace [1,0] [1,0]).1 = (twoSeedTrace [0,1] [1,0]).1 ∧
    (twoSeedTrace [1,0] [1,0]).2 ≠ (twoSeedTrace [0,1] [1,0]).2 := by decide

/-- Same accepted candidate, different rejection/refill/address trace. -/
theorem accepted_value_not_trace :
    (rejectionTrace (fun _ => 1) 2 0 ⟨8,0⟩).1 =
      (rejectionTrace (fun i => if i == 0 then 2147483647 else 1) 2 0 ⟨8,0⟩).1 ∧
    (rejectionTrace (fun _ => 1) 2 0 ⟨8,0⟩).2.2 ≠
      (rejectionTrace (fun i => if i == 0 then 2147483647 else 1) 2 0 ⟨8,0⟩).2.2 := by
  constructor <;> simp [rejectionTrace, nextTrace, branch]

#print axioms trace_congr
#print axioms nonzero_verdict_not_trace
#print axioms accepted_value_not_trace
end R1Z.L2Leaf_Trace
