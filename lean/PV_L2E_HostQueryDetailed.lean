import PV_L2E_QueryMemberTrace
set_option autoImplicit false
namespace PV_L2E_HostQueryDetailed
open PV_L2D_QueryScan PV_L2E_HostQuery

inductive Event where
  | base (e : PV_L2E_HostQuery.Event)
  | member (e : PV_L2E_QueryMemberTrace.Event)
  | blockGuard (index : Nat) (valid : Bool)
  | byteGuard (index : Nat) (valid : Bool)
  | writeGuard (index : Nat) (valid : Bool)
  | advanceGuard (index : Nat) (valid : Bool)
  | duplicateBranch (duplicate : Bool)
  | recurse (draws : Nat)
  deriving DecidableEq

def readBytes (draws : Nat) : List Event :=
  [.blockGuard (draws/8) (decide (draws/8<8))] ++
    ([4*(draws%8),4*(draws%8)+1,4*(draws%8)+2,4*(draws%8)+3].flatMap fun offset =>
      [.byteGuard offset (decide (offset<32)),.base (.readByte (draws/8) offset)])

def success (s : State) (k : Nat) (cap : Bool) : Result × List Event :=
  (.ok s.accepted k,[.base (.drawGuard cap),.base (.acceptedGuard true),
    .advanceGuard k (decide (k<8)),.base (.selectAdvance k)])

/-- A richer host observer retaining nested membership loop guards, each
array bound, duplicate branch and recursive continuation. Raw words are still
an explicit input; this is not the whole prover's native machine. -/
def run (s : State) (words : List Nat) : Result × List Event :=
  if s.draws=64 then
    if s.accepted.length=22 then success s 7 true
    else (.exhausted,[.base (.drawGuard true),.base (.acceptedGuard false)])
  else if s.accepted.length=22 then success s (s.draws/8) false
  else match words with
    | [] => (.missingWord,[.base (.drawGuard false),.base (.acceptedGuard false)])
    | x::xs =>
      let m := PV_L2E_QueryMemberTrace.run x 0 s.accepted
      let tail := run (next s x) xs
      (tail.1,[.base (.drawGuard false),.base (.acceptedGuard false)] ++
        readBytes s.draws ++ m.2.map Event.member ++ [.duplicateBranch m.1] ++
        (if m.1 then [] else [.writeGuard s.accepted.length (decide (s.accepted.length<22)),
          .base (.writeQuery s.accepted.length)]) ++ [.recurse (s.draws+1)] ++ tail.2)
termination_by words.length

theorem complete_result (s : State) (words : List Nat) :
    (run s words).1=(PV_L2E_HostQuery.run s words).1 := by
  induction words generalizing s with
  | nil =>
    rw [run.eq_def,PV_L2E_HostQuery.run.eq_def]
    split_ifs <;> rfl
  | cons x xs ih =>
    rw [run.eq_def,PV_L2E_HostQuery.run.eq_def]
    split_ifs <;> first | rfl | exact ih (next s x)

theorem no_missing (s : State) (words : List Nat) (remaining : s.draws+words.length=64) :
    (run s words).1≠.missingWord := by
  rw [complete_result]
  exact PV_L2E_HostQueryValue.no_missing_word s words remaining

/-- Each recursive call consumes exactly one input word, so complete
64-word inputs cannot diverge inside this scanner. -/
theorem next_fuel (s : State) (x : Nat) (xs : List Nat)
    (remaining : s.draws+(x::xs).length=64) : (next s x).draws+xs.length=64 := by
  simp only [next,List.length_cons] at remaining ⊢
  omega

#print axioms complete_result
#print axioms no_missing
#print axioms next_fuel
end PV_L2E_HostQueryDetailed
