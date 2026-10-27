import RPz8_F3R_Rounds
import RPz8_F3R_TraceHead
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_RoundsTrace
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog

theorem log {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (B : RoundModel.Boundaries)
    {before after : r1_wire.SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (trace : SourceFull25.Trace D pre before after cs)
    (order : cs.map (fun c=>c.row.val)=(List.range 10).map (fun j=>15+j))
    (out : aspis_core.field.QM31 × Array aspis_core.field.QM31 10#usize × r1_wire.SemanticTranscript Hash)
    (success : erase (S1SemanticCode.rounds B D pre before)=ok (.Ok out)) :
    observe (run (S1SemanticCode.rounds B D pre before)).1=sourceLog cs := by
  have count : cs.length=10 := by
    have h := congrArg List.length order
    simpa only [List.length_map,List.length_range] using h
  rcases cs with _ | ⟨c15,cs⟩
  · simp only [List.length_cons,List.length_nil] at count
    omega
  ·
    rcases cs with _ | ⟨c16,cs⟩
    · simp only [List.length_cons,List.length_nil] at count
      omega
    ·
      rcases cs with _ | ⟨c17,cs⟩
      · simp only [List.length_cons,List.length_nil] at count
        omega
      ·
        rcases cs with _ | ⟨c18,cs⟩
        · simp only [List.length_cons,List.length_nil] at count
          omega
        ·
          rcases cs with _ | ⟨c19,cs⟩
          · simp only [List.length_cons,List.length_nil] at count
            omega
          ·
            rcases cs with _ | ⟨c20,cs⟩
            · simp only [List.length_cons,List.length_nil] at count
              omega
            ·
              rcases cs with _ | ⟨c21,cs⟩
              · simp only [List.length_cons,List.length_nil] at count
                omega
              ·
                rcases cs with _ | ⟨c22,cs⟩
                · simp only [List.length_cons,List.length_nil] at count
                  omega
                ·
                  rcases cs with _ | ⟨c23,cs⟩
                  · simp only [List.length_cons,List.length_nil] at count
                    omega
                  ·
                    rcases cs with _ | ⟨c24,cs⟩
                    · simp only [List.length_cons,List.length_nil] at count
                      omega
                    ·
                      have empty : cs=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at count;omega)
                      subst cs
                      change [c15.row.val,c16.row.val,c17.row.val,c18.row.val,c19.row.val,c20.row.val,c21.row.val,c22.row.val,c23.row.val,c24.row.val]=[15,16,17,18,19,20,21,22,23,24] at order
                      simp only [List.cons.injEq] at order
                      rcases order with ⟨h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,last⟩
                      have row15 : c15.row=15#u8 := UScalar.eq_of_val_eq h15
                      have row16 : c16.row=16#u8 := UScalar.eq_of_val_eq h16
                      have row17 : c17.row=17#u8 := UScalar.eq_of_val_eq h17
                      have row18 : c18.row=18#u8 := UScalar.eq_of_val_eq h18
                      have row19 : c19.row=19#u8 := UScalar.eq_of_val_eq h19
                      have row20 : c20.row=20#u8 := UScalar.eq_of_val_eq h20
                      have row21 : c21.row=21#u8 := UScalar.eq_of_val_eq h21
                      have row22 : c22.row=22#u8 := UScalar.eq_of_val_eq h22
                      have row23 : c23.row=23#u8 := UScalar.eq_of_val_eq h23
                      have row24 : c24.row=24#u8 := UScalar.eq_of_val_eq h24
                      obtain ⟨first,t16⟩ := F3R_TraceHead.head c15 _ trace
                      obtain ⟨same16,t17⟩ := F3R_TraceHead.head c16 _ t16
                      obtain ⟨same17,t18⟩ := F3R_TraceHead.head c17 _ t17
                      obtain ⟨same18,t19⟩ := F3R_TraceHead.head c18 _ t18
                      obtain ⟨same19,t20⟩ := F3R_TraceHead.head c19 _ t19
                      obtain ⟨same20,t21⟩ := F3R_TraceHead.head c20 _ t20
                      obtain ⟨same21,t22⟩ := F3R_TraceHead.head c21 _ t21
                      obtain ⟨same22,t23⟩ := F3R_TraceHead.head c22 _ t22
                      obtain ⟨same23,t24⟩ := F3R_TraceHead.head c23 _ t23
                      obtain ⟨same24,t25⟩ := F3R_TraceHead.head c24 _ t24
                      rw [first] at success ⊢
                      rw [F3R_Rounds.log B c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 row15 row16 row17 row18 row19 row20 row21 row22 row23 row24 same16.symm same17.symm same18.symm same19.symm same20.symm same21.symm same22.symm same23.symm same24.symm out success]
                      simp only [sourceLog,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

#print axioms log
end AspisR1.F3R_RoundsTrace
end
