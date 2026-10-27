import RPz8_F3T_AcceptedParser
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_InitialConstructor
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem initial (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (i : F3_Model.Input)
    (accepted : (eval H (F3_Model.verifier D i)).2=true) :
    ∃ root word,i.proof 0=.initial root word := by
  obtain ⟨p,parsed,wire,aligned⟩ := F3T_AcceptedParser.parsed D H i accepted
  obtain ⟨root,initial,bytes⟩ := F3T_AlignedRows.initial D H i.semantic.value i.proof p aligned
  cases first : i.proof 0 with
  | initial r w=>exact ⟨r,w,rfl⟩
  | payload b=>simp only [first,LiteralTranscript.erase,reduceCtorEq] at initial
  | c2 b w=>simp only [first,LiteralTranscript.erase,reduceCtorEq] at initial
  | second b w=>simp only [first,LiteralTranscript.erase,reduceCtorEq] at initial

#print axioms initial
end AspisR1.F3T_InitialConstructor
end
