import NIH_RustBind
import NGX_PrefixSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_PrefixFrames
open AspisR1PrefixAggregateParser
/-- Generic predecessor provenance on the retained emitted aggregate parser.
The actual parseAt frame law remains a named callee obligation. -/
theorem result
 (parseAt : Slice U8→U8→Usize→Result (core.result.Result (Slice U8×Usize) r1_wire.Error))
 (bytes : Slice U8) (prefix : r1_wire.Prefix)
 (law : ∀ row offset frame finish,parseAt bytes row offset=ok (.Ok (frame,finish)) →
   frame.val.length=NGX_PrefixGeometry.width row.val)
 (run : NGX_PrefixSource.computation parseAt bytes=ok (.Ok prefix)) :
 ∀ i : Fin 27,(FJb_TailCell.cell prefix.records i).val.length=NGX_PrefixGeometry.width i.val := by
 unfold NGX_PrefixSource.computation at run
 split at run
 · cases run
 · obtain ⟨slice,_,run⟩:=FIv_Map.bind_success _ _ _ run
   obtain ⟨reply,_,run⟩:=FIv_Map.bind_success _ _ _ run
   cases reply with
   | Err e=>cases run
   | Ok root=>
    change NIH_RustBind.next (parseAt bytes 0#u8 32#usize) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame0,offset0⟩,step0,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h0:=law 0#u8 32#usize frame0 offset0 step0
    change NIH_RustBind.next (parseAt bytes 1#u8 offset0) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame1,offset1⟩,step1,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h1:=law 1#u8 offset0 frame1 offset1 step1
    change NIH_RustBind.next (parseAt bytes 2#u8 offset1) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame2,offset2⟩,step2,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h2:=law 2#u8 offset1 frame2 offset2 step2
    change NIH_RustBind.next (parseAt bytes 3#u8 offset2) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame3,offset3⟩,step3,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h3:=law 3#u8 offset2 frame3 offset3 step3
    change NIH_RustBind.next (parseAt bytes 4#u8 offset3) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame4,offset4⟩,step4,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h4:=law 4#u8 offset3 frame4 offset4 step4
    change NIH_RustBind.next (parseAt bytes 5#u8 offset4) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame5,offset5⟩,step5,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h5:=law 5#u8 offset4 frame5 offset5 step5
    change NIH_RustBind.next (parseAt bytes 6#u8 offset5) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame6,offset6⟩,step6,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h6:=law 6#u8 offset5 frame6 offset6 step6
    change NIH_RustBind.next (parseAt bytes 7#u8 offset6) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame7,offset7⟩,step7,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h7:=law 7#u8 offset6 frame7 offset7 step7
    change NIH_RustBind.next (parseAt bytes 8#u8 offset7) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame8,offset8⟩,step8,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h8:=law 8#u8 offset7 frame8 offset8 step8
    change NIH_RustBind.next (parseAt bytes 9#u8 offset8) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame9,offset9⟩,step9,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h9:=law 9#u8 offset8 frame9 offset9 step9
    change NIH_RustBind.next (parseAt bytes 10#u8 offset9) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame10,offset10⟩,step10,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h10:=law 10#u8 offset9 frame10 offset10 step10
    change NIH_RustBind.next (parseAt bytes 11#u8 offset10) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame11,offset11⟩,step11,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h11:=law 11#u8 offset10 frame11 offset11 step11
    change NIH_RustBind.next (parseAt bytes 12#u8 offset11) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame12,offset12⟩,step12,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h12:=law 12#u8 offset11 frame12 offset12 step12
    change NIH_RustBind.next (parseAt bytes 13#u8 offset12) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame13,offset13⟩,step13,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h13:=law 13#u8 offset12 frame13 offset13 step13
    change NIH_RustBind.next (parseAt bytes 14#u8 offset13) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame14,offset14⟩,step14,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h14:=law 14#u8 offset13 frame14 offset14 step14
    change NIH_RustBind.next (parseAt bytes 15#u8 offset14) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame15,offset15⟩,step15,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h15:=law 15#u8 offset14 frame15 offset15 step15
    change NIH_RustBind.next (parseAt bytes 16#u8 offset15) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame16,offset16⟩,step16,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h16:=law 16#u8 offset15 frame16 offset16 step16
    change NIH_RustBind.next (parseAt bytes 17#u8 offset16) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame17,offset17⟩,step17,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h17:=law 17#u8 offset16 frame17 offset17 step17
    change NIH_RustBind.next (parseAt bytes 18#u8 offset17) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame18,offset18⟩,step18,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h18:=law 18#u8 offset17 frame18 offset18 step18
    change NIH_RustBind.next (parseAt bytes 19#u8 offset18) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame19,offset19⟩,step19,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h19:=law 19#u8 offset18 frame19 offset19 step19
    change NIH_RustBind.next (parseAt bytes 20#u8 offset19) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame20,offset20⟩,step20,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h20:=law 20#u8 offset19 frame20 offset20 step20
    change NIH_RustBind.next (parseAt bytes 21#u8 offset20) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame21,offset21⟩,step21,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h21:=law 21#u8 offset20 frame21 offset21 step21
    change NIH_RustBind.next (parseAt bytes 22#u8 offset21) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame22,offset22⟩,step22,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h22:=law 22#u8 offset21 frame22 offset22 step22
    change NIH_RustBind.next (parseAt bytes 23#u8 offset22) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame23,offset23⟩,step23,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h23:=law 23#u8 offset22 frame23 offset23 step23
    change NIH_RustBind.next (parseAt bytes 24#u8 offset23) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame24,offset24⟩,step24,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h24:=law 24#u8 offset23 frame24 offset24 step24
    change NIH_RustBind.next (parseAt bytes 25#u8 offset24) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame25,offset25⟩,step25,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h25:=law 25#u8 offset24 frame25 offset25 step25
    change NIH_RustBind.next (parseAt bytes 26#u8 offset25) _ =
      (ok (core.result.Result.Ok prefix) : Result (core.result.Result r1_wire.Prefix r1_wire.Error)) at run
    obtain ⟨⟨frame26,offset26⟩,step26,run⟩:=NIH_RustBind.continued _ _ prefix run
    have h26:=law 26#u8 offset25 frame26 offset26 step26
    split at run
    · cases run
    · have same:=core.result.Result.Ok.inj (Result.ok.inj run)
      subst prefix
      intro i
      fin_cases i
      · simpa only [FJb_TailCell.cell,Array.make,show (0#u8).val=0 from rfl] using h0
      · simpa only [FJb_TailCell.cell,Array.make,show (1#u8).val=1 from rfl] using h1
      · simpa only [FJb_TailCell.cell,Array.make,show (2#u8).val=2 from rfl] using h2
      · simpa only [FJb_TailCell.cell,Array.make,show (3#u8).val=3 from rfl] using h3
      · simpa only [FJb_TailCell.cell,Array.make,show (4#u8).val=4 from rfl] using h4
      · simpa only [FJb_TailCell.cell,Array.make,show (5#u8).val=5 from rfl] using h5
      · simpa only [FJb_TailCell.cell,Array.make,show (6#u8).val=6 from rfl] using h6
      · simpa only [FJb_TailCell.cell,Array.make,show (7#u8).val=7 from rfl] using h7
      · simpa only [FJb_TailCell.cell,Array.make,show (8#u8).val=8 from rfl] using h8
      · simpa only [FJb_TailCell.cell,Array.make,show (9#u8).val=9 from rfl] using h9
      · simpa only [FJb_TailCell.cell,Array.make,show (10#u8).val=10 from rfl] using h10
      · simpa only [FJb_TailCell.cell,Array.make,show (11#u8).val=11 from rfl] using h11
      · simpa only [FJb_TailCell.cell,Array.make,show (12#u8).val=12 from rfl] using h12
      · simpa only [FJb_TailCell.cell,Array.make,show (13#u8).val=13 from rfl] using h13
      · simpa only [FJb_TailCell.cell,Array.make,show (14#u8).val=14 from rfl] using h14
      · simpa only [FJb_TailCell.cell,Array.make,show (15#u8).val=15 from rfl] using h15
      · simpa only [FJb_TailCell.cell,Array.make,show (16#u8).val=16 from rfl] using h16
      · simpa only [FJb_TailCell.cell,Array.make,show (17#u8).val=17 from rfl] using h17
      · simpa only [FJb_TailCell.cell,Array.make,show (18#u8).val=18 from rfl] using h18
      · simpa only [FJb_TailCell.cell,Array.make,show (19#u8).val=19 from rfl] using h19
      · simpa only [FJb_TailCell.cell,Array.make,show (20#u8).val=20 from rfl] using h20
      · simpa only [FJb_TailCell.cell,Array.make,show (21#u8).val=21 from rfl] using h21
      · simpa only [FJb_TailCell.cell,Array.make,show (22#u8).val=22 from rfl] using h22
      · simpa only [FJb_TailCell.cell,Array.make,show (23#u8).val=23 from rfl] using h23
      · simpa only [FJb_TailCell.cell,Array.make,show (24#u8).val=24 from rfl] using h24
      · simpa only [FJb_TailCell.cell,Array.make,show (25#u8).val=25 from rfl] using h25
      · simpa only [FJb_TailCell.cell,Array.make,show (26#u8).val=26 from rfl] using h26
#print axioms result
end AspisR1.NIH_PrefixFrames
