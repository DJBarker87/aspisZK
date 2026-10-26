import F3R_Begin
import F3R_TraceHead
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_BeginTrace
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog

theorem log {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {before after : r1_wire.SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (trace : SourceFull25.Trace D pre before after cs)
    (order : cs.map (fun c=>c.row.val)=List.range 15) :
    observe (run (S1SemanticCode.begin D pre before)).1=sourceLog cs := by
  have count : cs.length=15 := by
    have h := congrArg List.length order
    simpa only [List.length_map,List.length_range] using h
  rcases cs with _ | ⟨c0,cs⟩
  · simp only [List.length_cons,List.length_nil] at count
    omega
  ·
    rcases cs with _ | ⟨c1,cs⟩
    · simp only [List.length_cons,List.length_nil] at count
      omega
    ·
      rcases cs with _ | ⟨c2,cs⟩
      · simp only [List.length_cons,List.length_nil] at count
        omega
      ·
        rcases cs with _ | ⟨c3,cs⟩
        · simp only [List.length_cons,List.length_nil] at count
          omega
        ·
          rcases cs with _ | ⟨c4,cs⟩
          · simp only [List.length_cons,List.length_nil] at count
            omega
          ·
            rcases cs with _ | ⟨c5,cs⟩
            · simp only [List.length_cons,List.length_nil] at count
              omega
            ·
              rcases cs with _ | ⟨c6,cs⟩
              · simp only [List.length_cons,List.length_nil] at count
                omega
              ·
                rcases cs with _ | ⟨c7,cs⟩
                · simp only [List.length_cons,List.length_nil] at count
                  omega
                ·
                  rcases cs with _ | ⟨c8,cs⟩
                  · simp only [List.length_cons,List.length_nil] at count
                    omega
                  ·
                    rcases cs with _ | ⟨c9,cs⟩
                    · simp only [List.length_cons,List.length_nil] at count
                      omega
                    ·
                      rcases cs with _ | ⟨c10,cs⟩
                      · simp only [List.length_cons,List.length_nil] at count
                        omega
                      ·
                        rcases cs with _ | ⟨c11,cs⟩
                        · simp only [List.length_cons,List.length_nil] at count
                          omega
                        ·
                          rcases cs with _ | ⟨c12,cs⟩
                          · simp only [List.length_cons,List.length_nil] at count
                            omega
                          ·
                            rcases cs with _ | ⟨c13,cs⟩
                            · simp only [List.length_cons,List.length_nil] at count
                              omega
                            ·
                              rcases cs with _ | ⟨c14,cs⟩
                              · simp only [List.length_cons,List.length_nil] at count
                                omega
                              ·
                                have empty : cs=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at count;omega)
                                subst cs
                                change [c0.row.val,c1.row.val,c2.row.val,c3.row.val,c4.row.val,c5.row.val,c6.row.val,c7.row.val,c8.row.val,c9.row.val,c10.row.val,c11.row.val,c12.row.val,c13.row.val,c14.row.val]=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] at order
                                simp only [List.cons.injEq] at order
                                rcases order with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,last⟩
                                have row0 : c0.row=0#u8 := UScalar.eq_of_val_eq h0
                                have row1 : c1.row=1#u8 := UScalar.eq_of_val_eq h1
                                have row2 : c2.row=2#u8 := UScalar.eq_of_val_eq h2
                                have row3 : c3.row=3#u8 := UScalar.eq_of_val_eq h3
                                have row4 : c4.row=4#u8 := UScalar.eq_of_val_eq h4
                                have row5 : c5.row=5#u8 := UScalar.eq_of_val_eq h5
                                have row6 : c6.row=6#u8 := UScalar.eq_of_val_eq h6
                                have row7 : c7.row=7#u8 := UScalar.eq_of_val_eq h7
                                have row8 : c8.row=8#u8 := UScalar.eq_of_val_eq h8
                                have row9 : c9.row=9#u8 := UScalar.eq_of_val_eq h9
                                have row10 : c10.row=10#u8 := UScalar.eq_of_val_eq h10
                                have row11 : c11.row=11#u8 := UScalar.eq_of_val_eq h11
                                have row12 : c12.row=12#u8 := UScalar.eq_of_val_eq h12
                                have row13 : c13.row=13#u8 := UScalar.eq_of_val_eq h13
                                have row14 : c14.row=14#u8 := UScalar.eq_of_val_eq h14
                                obtain ⟨first,t1⟩ := F3R_TraceHead.head c0 _ trace
                                obtain ⟨same1,t2⟩ := F3R_TraceHead.head c1 _ t1
                                obtain ⟨same2,t3⟩ := F3R_TraceHead.head c2 _ t2
                                obtain ⟨same3,t4⟩ := F3R_TraceHead.head c3 _ t3
                                obtain ⟨same4,t5⟩ := F3R_TraceHead.head c4 _ t4
                                obtain ⟨same5,t6⟩ := F3R_TraceHead.head c5 _ t5
                                obtain ⟨same6,t7⟩ := F3R_TraceHead.head c6 _ t6
                                obtain ⟨same7,t8⟩ := F3R_TraceHead.head c7 _ t7
                                obtain ⟨same8,t9⟩ := F3R_TraceHead.head c8 _ t8
                                obtain ⟨same9,t10⟩ := F3R_TraceHead.head c9 _ t9
                                obtain ⟨same10,t11⟩ := F3R_TraceHead.head c10 _ t10
                                obtain ⟨same11,t12⟩ := F3R_TraceHead.head c11 _ t11
                                obtain ⟨same12,t13⟩ := F3R_TraceHead.head c12 _ t12
                                obtain ⟨same13,t14⟩ := F3R_TraceHead.head c13 _ t13
                                obtain ⟨same14,t15⟩ := F3R_TraceHead.head c14 _ t14
                                rw [first,F3R_Begin.log c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11 row12 row13 row14 same1.symm same2.symm same3.symm same4.symm same5.symm same6.symm same7.symm same8.symm same9.symm same10.symm same11.symm same12.symm same13.symm same14.symm]
                                simp only [sourceLog,List.append_assoc]

#print axioms log
end AspisR1.F3R_BeginTrace
end
