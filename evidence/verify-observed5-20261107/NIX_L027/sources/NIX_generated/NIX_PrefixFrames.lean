import NIH_RustBind
import NGX_PrefixSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Aeneas Aeneas.Std Result
namespace AspisR1.NIX_PrefixFrames
open AspisR1PrefixAggregateParser
/-- Generic predecessor provenance on the retained emitted aggregate parser.
The actual parseAt frame law remains a named callee obligation. -/
theorem result
 (parseAt : Slice U8→U8→Usize→Result (core.result.Result (Slice U8×Usize) r1_wire.Error))
 (bytes : Slice U8) (parsedPrefix : r1_wire.Prefix)
 (law : ∀ row offset frame finish,parseAt bytes row offset=ok (.Ok (frame,finish)) →
   frame.val.length=NGX_PrefixGeometry.width row.val)
 (run : NGX_PrefixSource.computation parseAt bytes=ok (.Ok parsedPrefix)) :
 ∀ i : Fin 27,(FJb_TailCell.cell parsedPrefix.records i).val.length=NGX_PrefixGeometry.width i.val := by
 unfold NGX_PrefixSource.computation at run
 change (if Slice.len bytes < 32#usize then _ else _) = _ at run
 by_cases short : Slice.len bytes < 32#usize
 · rw [if_pos short] at run
   cases run
 · rw [if_neg short] at run
   obtain ⟨slice,_,run⟩:=FIv_Map.bind_success _ _ _ run
   obtain ⟨reply,_,run⟩:=FIv_Map.bind_success _ _ _ run
   cases reply with
   | Err e=>cases run
   | Ok root=>
    obtain ⟨reply0,step0,run⟩:=FIv_Map.bind_success _ _ _ run
    cases reply0 with
    | Err e=>cases run
    | Ok pair=>
     rcases pair with ⟨frame0,offset0⟩
     rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
     have h0:=law 0#u8 32#usize frame0 offset0 step0
     obtain ⟨reply1,step1,run⟩:=FIv_Map.bind_success _ _ _ run
     cases reply1 with
     | Err e=>cases run
     | Ok pair=>
      rcases pair with ⟨frame1,offset1⟩
      rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
      have h1:=law 1#u8 offset0 frame1 offset1 step1
      obtain ⟨reply2,step2,run⟩:=FIv_Map.bind_success _ _ _ run
      cases reply2 with
      | Err e=>cases run
      | Ok pair=>
       rcases pair with ⟨frame2,offset2⟩
       rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
       have h2:=law 2#u8 offset1 frame2 offset2 step2
       obtain ⟨reply3,step3,run⟩:=FIv_Map.bind_success _ _ _ run
       cases reply3 with
       | Err e=>cases run
       | Ok pair=>
        rcases pair with ⟨frame3,offset3⟩
        rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
        have h3:=law 3#u8 offset2 frame3 offset3 step3
        obtain ⟨reply4,step4,run⟩:=FIv_Map.bind_success _ _ _ run
        cases reply4 with
        | Err e=>cases run
        | Ok pair=>
         rcases pair with ⟨frame4,offset4⟩
         rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
         have h4:=law 4#u8 offset3 frame4 offset4 step4
         obtain ⟨reply5,step5,run⟩:=FIv_Map.bind_success _ _ _ run
         cases reply5 with
         | Err e=>cases run
         | Ok pair=>
          rcases pair with ⟨frame5,offset5⟩
          rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
          have h5:=law 5#u8 offset4 frame5 offset5 step5
          obtain ⟨reply6,step6,run⟩:=FIv_Map.bind_success _ _ _ run
          cases reply6 with
          | Err e=>cases run
          | Ok pair=>
           rcases pair with ⟨frame6,offset6⟩
           rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
           have h6:=law 6#u8 offset5 frame6 offset6 step6
           obtain ⟨reply7,step7,run⟩:=FIv_Map.bind_success _ _ _ run
           cases reply7 with
           | Err e=>cases run
           | Ok pair=>
            rcases pair with ⟨frame7,offset7⟩
            rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
            have h7:=law 7#u8 offset6 frame7 offset7 step7
            obtain ⟨reply8,step8,run⟩:=FIv_Map.bind_success _ _ _ run
            cases reply8 with
            | Err e=>cases run
            | Ok pair=>
             rcases pair with ⟨frame8,offset8⟩
             rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
             have h8:=law 8#u8 offset7 frame8 offset8 step8
             obtain ⟨reply9,step9,run⟩:=FIv_Map.bind_success _ _ _ run
             cases reply9 with
             | Err e=>cases run
             | Ok pair=>
              rcases pair with ⟨frame9,offset9⟩
              rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
              have h9:=law 9#u8 offset8 frame9 offset9 step9
              obtain ⟨reply10,step10,run⟩:=FIv_Map.bind_success _ _ _ run
              cases reply10 with
              | Err e=>cases run
              | Ok pair=>
               rcases pair with ⟨frame10,offset10⟩
               rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
               have h10:=law 10#u8 offset9 frame10 offset10 step10
               obtain ⟨reply11,step11,run⟩:=FIv_Map.bind_success _ _ _ run
               cases reply11 with
               | Err e=>cases run
               | Ok pair=>
                rcases pair with ⟨frame11,offset11⟩
                rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                have h11:=law 11#u8 offset10 frame11 offset11 step11
                obtain ⟨reply12,step12,run⟩:=FIv_Map.bind_success _ _ _ run
                cases reply12 with
                | Err e=>cases run
                | Ok pair=>
                 rcases pair with ⟨frame12,offset12⟩
                 rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                 have h12:=law 12#u8 offset11 frame12 offset12 step12
                 obtain ⟨reply13,step13,run⟩:=FIv_Map.bind_success _ _ _ run
                 cases reply13 with
                 | Err e=>cases run
                 | Ok pair=>
                  rcases pair with ⟨frame13,offset13⟩
                  rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                  have h13:=law 13#u8 offset12 frame13 offset13 step13
                  obtain ⟨reply14,step14,run⟩:=FIv_Map.bind_success _ _ _ run
                  cases reply14 with
                  | Err e=>cases run
                  | Ok pair=>
                   rcases pair with ⟨frame14,offset14⟩
                   rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                   have h14:=law 14#u8 offset13 frame14 offset14 step14
                   obtain ⟨reply15,step15,run⟩:=FIv_Map.bind_success _ _ _ run
                   cases reply15 with
                   | Err e=>cases run
                   | Ok pair=>
                    rcases pair with ⟨frame15,offset15⟩
                    rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                    have h15:=law 15#u8 offset14 frame15 offset15 step15
                    obtain ⟨reply16,step16,run⟩:=FIv_Map.bind_success _ _ _ run
                    cases reply16 with
                    | Err e=>cases run
                    | Ok pair=>
                     rcases pair with ⟨frame16,offset16⟩
                     rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                     have h16:=law 16#u8 offset15 frame16 offset16 step16
                     obtain ⟨reply17,step17,run⟩:=FIv_Map.bind_success _ _ _ run
                     cases reply17 with
                     | Err e=>cases run
                     | Ok pair=>
                      rcases pair with ⟨frame17,offset17⟩
                      rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                      have h17:=law 17#u8 offset16 frame17 offset17 step17
                      obtain ⟨reply18,step18,run⟩:=FIv_Map.bind_success _ _ _ run
                      cases reply18 with
                      | Err e=>cases run
                      | Ok pair=>
                       rcases pair with ⟨frame18,offset18⟩
                       rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                       have h18:=law 18#u8 offset17 frame18 offset18 step18
                       obtain ⟨reply19,step19,run⟩:=FIv_Map.bind_success _ _ _ run
                       cases reply19 with
                       | Err e=>cases run
                       | Ok pair=>
                        rcases pair with ⟨frame19,offset19⟩
                        rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                        have h19:=law 19#u8 offset18 frame19 offset19 step19
                        obtain ⟨reply20,step20,run⟩:=FIv_Map.bind_success _ _ _ run
                        cases reply20 with
                        | Err e=>cases run
                        | Ok pair=>
                         rcases pair with ⟨frame20,offset20⟩
                         rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                         have h20:=law 20#u8 offset19 frame20 offset20 step20
                         obtain ⟨reply21,step21,run⟩:=FIv_Map.bind_success _ _ _ run
                         cases reply21 with
                         | Err e=>cases run
                         | Ok pair=>
                          rcases pair with ⟨frame21,offset21⟩
                          rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                          have h21:=law 21#u8 offset20 frame21 offset21 step21
                          obtain ⟨reply22,step22,run⟩:=FIv_Map.bind_success _ _ _ run
                          cases reply22 with
                          | Err e=>cases run
                          | Ok pair=>
                           rcases pair with ⟨frame22,offset22⟩
                           rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                           have h22:=law 22#u8 offset21 frame22 offset22 step22
                           obtain ⟨reply23,step23,run⟩:=FIv_Map.bind_success _ _ _ run
                           cases reply23 with
                           | Err e=>cases run
                           | Ok pair=>
                            rcases pair with ⟨frame23,offset23⟩
                            rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                            have h23:=law 23#u8 offset22 frame23 offset23 step23
                            obtain ⟨reply24,step24,run⟩:=FIv_Map.bind_success _ _ _ run
                            cases reply24 with
                            | Err e=>cases run
                            | Ok pair=>
                             rcases pair with ⟨frame24,offset24⟩
                             rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                             have h24:=law 24#u8 offset23 frame24 offset24 step24
                             obtain ⟨reply25,step25,run⟩:=FIv_Map.bind_success _ _ _ run
                             cases reply25 with
                             | Err e=>cases run
                             | Ok pair=>
                              rcases pair with ⟨frame25,offset25⟩
                              rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                              have h25:=law 25#u8 offset24 frame25 offset25 step25
                              obtain ⟨reply26,step26,run⟩:=FIv_Map.bind_success _ _ _ run
                              cases reply26 with
                              | Err e=>cases run
                              | Ok pair=>
                               rcases pair with ⟨frame26,offset26⟩
                               rw [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                               have h26:=law 26#u8 offset25 frame26 offset26 step26
                               split at run
                               · cases run
                               · have same:=core.result.Result.Ok.inj (Result.ok.inj run)
                                 subst parsedPrefix
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
end AspisR1.NIX_PrefixFrames
