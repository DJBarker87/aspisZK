import RPz7_S1QueryByteChainV1
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.PreparedHashCode.QueryPair
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

/-- The SAME concrete oracle execution supplies both full buffers and its
ordered log, independently of the pure output continuation. -/
theorem paired_eval_witness (n : Nat) (state : State) (blocks advances : List State)
    (oracle : Bytes → State) :
    ∃ (log : List (Bytes × State)) (bs xs : List State),
      bs.length=blocks.length+n ∧ xs.length=advances.length+n ∧
      ∀ {A : Type} (out : List State → List State → A),
        eval oracle (pairedBytesProgram out n state blocks advances)=(log,out bs xs) := by
  induction n generalizing state blocks advances with
  | zero => exact ⟨[],blocks,advances,by omega,by omega,fun _ => rfl⟩
  | succ n ih =>
    let qb := flatten (TranscriptStep.readParts (encodeState state) 1#u8)
    let qx := flatten (TranscriptStep.readParts (encodeState state) 2#u8)
    obtain ⟨log,bs,xs,hbs,hxs,heval⟩ :=
      ih (oracle qx) (blocks++[oracle qb]) (advances++[oracle qx])
    refine ⟨(qb,oracle qb)::(qx,oracle qx)::log,bs,xs,?_,?_,?_⟩
    · simp only [List.length_append,List.length_singleton] at hbs; omega
    · simp only [List.length_append,List.length_singleton] at hxs; omega
    · intro A out
      simpa only [pairedBytesProgram,eval] using
        congrArg (fun r => ((qb,oracle qb)::(qx,oracle qx)::r.1,r.2)) (heval out)

#print axioms paired_eval_witness
end AspisR1PublicPreparation.PreparedHashCode.QueryPair
