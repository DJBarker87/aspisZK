import S1OwnedQueryPairsStepModelV1
set_option autoImplicit false
namespace AspisS1OwnedQueryPairs.Model
open Aeneas Aeneas.Std Result
open AspisV8R19.SourceDuplexStep AspisV8R19.Q22WordScan AspisV8R19.SqueezeOracleBridge
abbrev SampleError := AspisS1OwnedQueryPairs.aspis_core.transcript.QuerySampleError
abbrev NativeResult := core.result.Result ((Array U32 22#usize) × Block) SampleError

def finishValue (s : OwnedScan) (selected : Block) : NativeResult :=
  if s.accepted_len=22#usize then .Ok (s.accepted,selected)
  else .Err (.DrawLimitExhausted s.accepted_len 64#usize)

theorem finish_eq (s : OwnedScan) (selected : Block) :
    pairs_finish s selected=ok (finishValue s selected) := by
  by_cases full : s.accepted_len=22#usize
  · simp only [pairs_finish,finishValue,if_pos full]
  · simp only [pairs_finish,finishValue,if_neg full]

/-- The native error enum stays complete. Only its reached exhaustion variant
can occur; its maximum andaccepted count are preserved exactly. -/
def ResultMeaning (source : NativeResult) (model : Except Nat (List Nat) × State) : Prop :=
  match source with
  | .Ok (queries,selected) => model=(.ok (queries.val.map (fun w => w.val)),decodeState selected)
  | .Err (.DrawLimitExhausted accepted maximum) => maximum=64#usize ∧ model.1=.error accepted.val
  | .Err (.BoundNotPowerOfTwo _) => False
  | .Err (.CountExceedsBound _ _) => False

theorem prefix_length (s : OwnedScan) (valid : Valid s) :
    (qState s).accepted.length=s.accepted_len.val := by
  simp only [qState,project,Query31ExplicitScanBody.q22StateOf,
    Query31ExplicitScanBody.acceptedPrefix,List.length_map,List.length_take,s.accepted.property]
  exact Nat.min_eq_left valid.1

/-- TOTAL exact finisher agreement, including rejected inputs. No successful
finish, full-length query array, or canonical query predicate is assumed. -/
theorem finish_meaning (s : OwnedScan) (selected : Block) (valid : Valid s) :
    ResultMeaning (finishValue s selected) (finish (qState s),decodeState selected) := by
  by_cases full : s.accepted_len=22#usize
  · simp only [finishValue,if_pos full,ResultMeaning]
    have fullNat : s.accepted_len.val=22 := by rw [full];rfl
    have len := prefix_length s valid
    have plen : (qState s).accepted.length=22 := len.trans fullNat
    simp only [finish,if_pos plen]
    have values : (qState s).accepted=s.accepted.val.map (fun w => w.val) := by
      simp only [qState,project,Query31ExplicitScanBody.q22StateOf,
        Query31ExplicitScanBody.acceptedPrefix,fullNat]
      have sourceLength : s.accepted.val.length=22 := s.accepted.property
      have take : s.accepted.val.take 22=s.accepted.val :=
        List.take_of_length_le (by omega)
      exact congrArg (fun xs : List U32 => xs.map (fun w => w.val)) take
    rw [values]
  · simp only [finishValue,if_neg full,ResultMeaning]
    have len := prefix_length s valid
    have notFull : (qState s).accepted.length≠22 := by rw [len];scalar_tac
    simp only [finish,if_neg notFull,len]
    exact ⟨True.intro,rfl⟩

#print axioms finish_eq
#print axioms prefix_length
#print axioms finish_meaning
end AspisS1OwnedQueryPairs.Model
