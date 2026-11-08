import NNH_Libraries
import NNH_ObservedReturns
import NNH_ExceptOk
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_ObservedCut
open RSL NNH_Libraries
/-- Canonical returned-path decomposition, retaining all SAME semantic values. -/
structure Packet (a : TX1_137.Args VL) (env : Env) (sem : Verified VL) where
 prefix_ : VL.Prefix
 initial : VL.Transcript
 challenges : VL.Challenges
 before : VL.Transcript
 parsed : LIB_VLib.parsePrefixValue a.bytes env = .ok prefix_
 initialized : LIB_VLib.publicTranscriptValue (a.public_,VL.c1Root prefix_) env = .ok initial
 begun : LIB_VLib.beginValue (prefix_,initial) env = .ok (challenges,before)
 finished : NNH_FinishReturns.value ⟨a.public_,prefix_,before,challenges⟩ env = .ok sem

theorem returned (a : TX1_137.Args VL) (env : Env) (sem : Verified VL)
 (called : NNH_ObservedReturns.value a env = .ok sem) :
 Nonempty (Packet a env sem) := by
 unfold NNH_ObservedReturns.value at called
 obtain ⟨pre,hp,called⟩ := NNH_ExceptOk.bind _ _ sem called
 obtain ⟨initial,hi,called⟩ := NNH_ExceptOk.bind _ _ sem called
 obtain ⟨⟨cs,before⟩,hb,called⟩ := NNH_ExceptOk.bind _ _ sem called
 exact ⟨⟨pre,initial,cs,before,hp,hi,hb,called⟩⟩
#print axioms returned
end AspisR1.NNV_ObservedCut
end
