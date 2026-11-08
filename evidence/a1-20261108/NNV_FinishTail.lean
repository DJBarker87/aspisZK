import NNV_FinishCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_FinishTail
open RSL NNH_Libraries NNH_ReturnedRE
abbrev V := NNH_FinishReturns.V
local instance : DecidableEq V.QM31 := V.qDec
local instance : DecidableEq V.Point := V.pDec
structure Packet (a : TX1_136.Args V) (env : Env) (sem : Verified V)
 (head : NNV_FinishCut.Packet a env sem) where
 terminal : V.QM31
 rec25 : V.Record
 extra : V.K29
 rec25' : V.Record
 c0 : V.Point × V.Transcript
 rec26 : V.Record
 beforeZ1 : V.K29
 rec26' : V.Record
 c1 : V.Point × V.Transcript
 payload : Bytes
 root1 : B32
 terminal_ok : RE.mapE (fun _ => V.wPublic)
  (LIB_VLib.terminalQm31Value (a.public_,head.claims,head.rounds.2.1,V.origChallenges a.challenges) env) = .ok terminal
 record25 : V.validatedRecord a.prefix_ 25 = .ok rec25
 decoded25 : V.decodeK29 rec25 87 = .ok extra
 gate : head.rounds.1 = V.qadd (V.qadd (V.maskValue head.claims head.rounds.2.1)
  (V.qmul (V.eta a.challenges) terminal)) (V.at28 extra)
 record25' : V.validatedRecord a.prefix_ 25 = .ok rec25'
 circle0 : LIB_VLib.circleValue (head.rounds.2.2,rec25') env = .ok c0
 record26 : V.validatedRecord a.prefix_ 26 = .ok rec26
 decoded26 : V.decodeK29 rec26 0 = .ok beforeZ1
 record26' : V.validatedRecord a.prefix_ 26 = .ok rec26'
 circle1 : LIB_VLib.circleValue (c0.2,rec26') env = .ok c1
 distinct : c0.1 ≠ c1.1
 payload_ok : V.payload a.prefix_ 2 = .ok payload
 root_ok : TX1_136.toB32 payload = some root1
 semantic : sem = ⟨(V.c1Root a.prefix_,root1),a.challenges,head.rounds.2.1,
  head.claims,extra,beforeZ1,V.state head.rounds.2.2,(c0.1,c1.1),c1.2⟩

theorem returned (a : TX1_136.Args V) (env : Env) (sem : Verified V)
 (head : NNV_FinishCut.Packet a env sem) : Nonempty (Packet a env sem head) := by
 have called := head.continuation
 obtain ⟨terminal,ht,called⟩ := NNH_ExceptOk.bind _ _ sem called
 obtain ⟨r25,hr25,called⟩ := NNH_ExceptOk.bind _ _ sem called
 obtain ⟨extra,he,called⟩ := NNH_ExceptOk.bind _ _ sem called
 obtain ⟨u,hgate,called⟩ := NNH_ExceptOk.bind _ _ sem called
 have gate : head.rounds.1 = V.qadd (V.qadd (V.maskValue head.claims head.rounds.2.1)
  (V.qmul (V.eta a.challenges) terminal)) (V.at28 extra) := by
  split at hgate
  · cases hgate
  · rename_i good
    simpa only [decide_eq_true_eq,not_not] using good
 obtain ⟨r25',hr25',called⟩ := NNH_ExceptOk.bind _ _ sem called
 obtain ⟨c0,hc0,called⟩ := NNH_ExceptOk.bind _ _ sem called
 obtain ⟨r26,hr26,called⟩ := NNH_ExceptOk.bind _ _ sem called
 obtain ⟨before,hb,called⟩ := NNH_ExceptOk.bind _ _ sem called
 obtain ⟨r26',hr26',called⟩ := NNH_ExceptOk.bind _ _ sem called
 obtain ⟨c1,hc1,called⟩ := NNH_ExceptOk.bind _ _ sem called
 obtain ⟨u',hd,called⟩ := NNH_ExceptOk.bind _ _ sem called
 have distinct : c0.1 ≠ c1.1 := by
  split at hd
  · cases hd
  · rename_i good
    simpa only [decide_eq_true_eq] using good
 obtain ⟨payload,hp,called⟩ := NNH_ExceptOk.bind _ _ sem called
 cases root : TX1_136.toB32 payload with
 | none => rw [root] at called; cases called
 | some root1 =>
  rw [root] at called
  exact ⟨⟨terminal,r25,extra,r25',c0,r26,before,r26',c1,payload,root1,
   ht,hr25,he,gate,hr25',hc0,hr26,hb,hr26',hc1,distinct,hp,root,(Except.ok.inj called).symm⟩⟩
#print axioms returned
end AspisR1.NNV_FinishTail
end
