import R1Z.PV_OWNJ_Points
set_option autoImplicit false
namespace R1Z.PV_OWNJ_FiatShamir
open PV_OWNI_RawOps
abbrev Bytes := List Nat
abbrev Hash := List Bytes → Bytes

def le32 (n : Nat) : Bytes := (List.range 4).map fun i => (n / 256^i) % 256

def domain : Bytes := [97,115,112,105,115,58,114,48,58,50,48,50,54,49,48,48,57,58,118,49]

def seed (hash : Hash) (public c1 : Bytes) : Bytes :=
 hash [domain,[0],le32 public.length,public,c1]

/-- One successful sample_block: absorb, squeeze from absorbed, advance from
absorbed. No polynomial evaluator or private column is an input. -/
def step (hash : Hash) (sample : Bytes → Q) (state : Bytes) (row : Nat) (framed : Bytes) : Q × Bytes :=
 let absorbed := hash [state,[0,160+row],framed]
 (sample (hash [absorbed,[1]]),hash [absorbed,[2]])

def replay (hash : Hash) (sample : Bytes → Q) : Bytes → Nat → List Bytes → List Q × Bytes
 | state,_,[] => ([],state)
 | state,row,framed::rest =>
  let result := step hash sample state row framed
  let tail := replay hash sample result.2 (row+1) rest
  (result.1::tail.1,tail.2)

def challenges (hash : Hash) (sample : Bytes → Q) (public c1 : Bytes) (published : List Bytes) : List Q :=
 (replay hash sample (seed hash public c1) 0 published).1

def alpha (hash : Hash) (sample : Bytes → Q) (public c1 : Bytes) (published : List Bytes) : List Q :=
 (challenges hash sample public c1 published).drop 15 |>.take 10

/-- Round/sample/assignment are deterministic loop counters. The prefix comes
from preceding semantic records, not from initial_claim or oracle output. -/
def query (sampleValue : Nat → Q) (alpha : List Q) (round sample assignment : Nat) : List Q :=
 alpha.take round ++ [sampleValue sample] ++
 (List.range (9-round)).map (fun offset =>
  if assignment.testBit (9-round-1-offset) then one else zero)

theorem replay_length (hash : Hash) (sample : Bytes → Q) (frames : List Bytes)
 (state : Bytes) (row : Nat) : (replay hash sample state row frames).1.length = frames.length := by
 induction frames generalizing state row with
 | nil => rfl
 | cons f fs ih => simp only [replay,List.length_cons,ih]

theorem alpha_length (hash : Hash) (sample : Bytes → Q) (public c1 : Bytes)
 (frames : List Bytes) (h : frames.length = 25) :
 (alpha hash sample public c1 frames).length = 10 := by
 simp only [alpha,List.length_take,List.length_drop,challenges,replay_length,h]

theorem query_public (sampleValue : Nat → Q) (hash : Hash) (sample : Bytes → Q) (public c1 : Bytes)
 (left right : List Bytes) (h : left = right) (round index assignment : Nat) :
 query sampleValue (alpha hash sample public c1 left) round index assignment =
 query sampleValue (alpha hash sample public c1 right) round index assignment := by rw [h]

theorem final_public (hash : Hash) (sample : Bytes → Q) (public c1 : Bytes)
 (left right : List Bytes) (h : left = right) :
 alpha hash sample public c1 left = alpha hash sample public c1 right := by rw [h]

/-- Appended future records do not change earlier challenge outputs. -/
theorem replay_append (hash : Hash) (sample : Bytes → Q) (frames tail : List Bytes)
 (state : Bytes) (row : Nat) :
 replay hash sample state row (frames ++ tail) =
 let prefix := replay hash sample state row frames
 let suffix := replay hash sample prefix.2 (row+frames.length) tail
 (prefix.1 ++ suffix.1,suffix.2) := by
 induction frames generalizing state row with
 | nil => simp only [List.nil_append,replay,List.length_nil,Nat.add_zero]
 | cons f fs ih =>
  simp only [List.cons_append,replay,ih,List.length_cons,Nat.add_succ,Nat.succ_add]

theorem query_length (sampleValue : Nat → Q) (a : List Q) (round index assignment : Nat)
 (ha : a.length = 10) (hr : round < 10) :
 (query sampleValue a round index assignment).length = 10 := by
 simp only [query,List.length_append,List.length_take,List.length_singleton,
  List.length_map,List.length_range,ha,Nat.min_eq_left (Nat.le_of_lt hr)]
 omega

#print axioms replay_length
#print axioms alpha_length
#print axioms query_public
#print axioms final_public
#print axioms replay_append
#print axioms query_length
end R1Z.PV_OWNJ_FiatShamir

