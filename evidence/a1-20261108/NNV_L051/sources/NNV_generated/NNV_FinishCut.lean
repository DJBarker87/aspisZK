import NNV_ObservedCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_FinishCut
open RSL NNH_Libraries
abbrev V := NNH_FinishReturns.V
local instance : DecidableEq V.QM31 := V.qDec
local instance : DecidableEq V.Point := V.pDec
structure Packet (a : TX1_136.Args V) (env : Env) (sem : Verified V) where
 rounds : V.QM31 × V.Alpha × V.Transcript
 claims : V.Claims
 rounded : LIB_VLib.semanticRoundsValue (a.prefix_,a.transcript) env = .ok rounds
 claimed : LIB_VLib.claimsValue a.prefix_ env = .ok claims
 continuation : NNH_ReturnedRE.bindValue
  (RE.mapE (fun _ => V.wPublic) (LIB_VLib.terminalQm31Value
   (a.public_,claims,rounds.2.1,V.origChallenges a.challenges) env)) (fun terminal =>
  NNH_ReturnedRE.bindValue (V.validatedRecord a.prefix_ 25) fun rec25 =>
  NNH_ReturnedRE.bindValue (V.decodeK29 rec25 87) fun extra =>
  let masked := V.qadd (V.qadd (V.maskValue claims rounds.2.1) (V.qmul (V.eta a.challenges) terminal)) (V.at28 extra)
  NNH_ReturnedRE.bindValue (if @decide (rounds.1 ≠ masked) (@instDecidableNot _ (V.qDec rounds.1 masked)) then .error V.wTerminal else .ok ()) fun _ =>
  NNH_ReturnedRE.bindValue (V.validatedRecord a.prefix_ 25) fun rec25' =>
  NNH_ReturnedRE.bindValue (LIB_VLib.circleValue (rounds.2.2,rec25') env) fun c0 =>
  NNH_ReturnedRE.bindValue (V.validatedRecord a.prefix_ 26) fun rec26 =>
  NNH_ReturnedRE.bindValue (V.decodeK29 rec26 0) fun beforeZ1 =>
  NNH_ReturnedRE.bindValue (V.validatedRecord a.prefix_ 26) fun rec26' =>
  NNH_ReturnedRE.bindValue (LIB_VLib.circleValue (c0.2,rec26') env) fun c1 =>
  NNH_ReturnedRE.bindValue (if @decide (c0.1 = c1.1) (V.pDec c0.1 c1.1) then .error V.wEqualCirclePoints else .ok ()) fun _ =>
  NNH_ReturnedRE.bindValue (V.payload a.prefix_ 2) fun p2 =>
  match TX1_136.toB32 p2 with
  | none => .error V.wPublic
  | some root1 => .ok ⟨(V.c1Root a.prefix_,root1),a.challenges,rounds.2.1,claims,extra,beforeZ1,V.state rounds.2.2,(c0.1,c1.1),c1.2⟩) = .ok sem

theorem returned (a : TX1_136.Args V) (env : Env) (sem : Verified V)
 (called : NNH_FinishReturns.value a env = .ok sem) : Nonempty (Packet a env sem) := by
 unfold NNH_FinishReturns.value at called
 obtain ⟨r,hr,called⟩ := NNH_ExceptOk.bind _ _ sem called
 obtain ⟨c,hc,called⟩ := NNH_ExceptOk.bind _ _ sem called
 exact ⟨⟨r,c,hr,hc,called⟩⟩
#print axioms returned
end AspisR1.NNV_FinishCut
end
