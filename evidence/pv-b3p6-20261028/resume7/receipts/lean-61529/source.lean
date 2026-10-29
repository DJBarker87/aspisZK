import PV_B3P_Success227
import PV_B3P_E227_14
import PV_B3P_Offset226V3
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

def MaskAllowed (m : U16) : Prop := m=1749#u16 ∨ m=2048#u16 ∨ m=2049#u16 ∨ m=4097#u16 ∨ m=6144#u16 ∨ m=6145#u16 ∨ m=26214#u16

theorem active_masks_allowed (m : U16)
    (hm : m ∈ reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val) : MaskAllowed m := by
  unfold reference_copy_terminal.constants.ACTIVE_ROW_MASKS at hm
  change m ∈ [6144#u16, 6144#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6144#u16, 4097#u16, 2048#u16, 6145#u16, 2049#u16, 2048#u16, 6145#u16, 2049#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 4097#u16, 6145#u16, 6145#u16, 4097#u16, 26214#u16, 26214#u16, 26214#u16, 26214#u16, 26214#u16, 26214#u16, 1749#u16] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h0))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h10)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h11)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h13)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h14)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h15)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h16)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h17)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h18)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h19)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h20)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h21)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h22)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h23)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h24)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h25))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h26)))
  · exact Or.inr (Or.inl h27)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h28)))))
  · exact Or.inr (Or.inr (Or.inl h29))
  · exact Or.inr (Or.inl h30)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h31)))))
  · exact Or.inr (Or.inr (Or.inl h32))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h33)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h34)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h35)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h36)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h37)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h38)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h39)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h40)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h41)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h42)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h43)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h44)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h45)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h46)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h47)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h48)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h49)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h50)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h51)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h52)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h53)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h54)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h55)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h56)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h57))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h58))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h59))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h60))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h61))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h62))))))
  · exact Or.inl h63

#print axioms active_masks_allowed

theorem mask_sum_total (values : Array aspis_core.field.QM31 16#usize) (mask : U16)
    (hm : MaskAllowed mask) : Success (reference_copy_terminal.selector_mask_sum_16 values mask) := by
  rcases hm with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst mask
    simp only [reference_copy_terminal.selector_mask_sum_16]
    apply bind
    · apply index <;> scalar_tac
    intro q
    apply bind
    · apply qadd
    intro q1
    apply bind
    · apply index <;> scalar_tac
    intro q2
    apply bind
    · apply qadd
    intro q3
    apply bind
    · apply index <;> scalar_tac
    intro q4
    apply bind
    · apply qadd
    intro q5
    apply bind
    · apply index <;> scalar_tac
    intro q6
    apply bind
    · apply qadd
    intro q7
    apply bind
    · apply index <;> scalar_tac
    intro q8
    apply bind
    · apply qadd
    intro q9
    apply bind
    · apply index <;> scalar_tac
    intro q10
    apply bind
    · apply qadd
    intro q11
    apply bind
    · apply index <;> scalar_tac
    intro q12
    apply qadd
  · subst mask
    simp only [reference_copy_terminal.selector_mask_sum_16]
    apply bind
    · apply index <;> scalar_tac
    intro q
    apply qadd
  · subst mask
    simp only [reference_copy_terminal.selector_mask_sum_16]
    apply bind
    · apply index <;> scalar_tac
    intro q
    apply bind
    · apply qadd
    intro q1
    apply bind
    · apply index <;> scalar_tac
    intro q2
    apply qadd
  · subst mask
    simp only [reference_copy_terminal.selector_mask_sum_16]
    apply bind
    · apply index <;> scalar_tac
    intro q
    apply bind
    · apply qadd
    intro q1
    apply bind
    · apply index <;> scalar_tac
    intro q2
    apply qadd
  · subst mask
    simp only [reference_copy_terminal.selector_mask_sum_16]
    apply bind
    · apply index <;> scalar_tac
    intro q
    apply bind
    · apply qadd
    intro q1
    apply bind
    · apply index <;> scalar_tac
    intro q2
    apply qadd
  · subst mask
    simp only [reference_copy_terminal.selector_mask_sum_16]
    apply bind
    · apply index <;> scalar_tac
    intro q
    apply bind
    · apply qadd
    intro q1
    apply bind
    · apply index <;> scalar_tac
    intro q2
    apply bind
    · apply qadd
    intro q3
    apply bind
    · apply index <;> scalar_tac
    intro q4
    apply qadd
  · subst mask
    simp only [reference_copy_terminal.selector_mask_sum_16]
    apply bind
    · apply index <;> scalar_tac
    intro q
    apply bind
    · apply qadd
    intro q1
    apply bind
    · apply index <;> scalar_tac
    intro q2
    apply bind
    · apply qadd
    intro q3
    apply bind
    · apply index <;> scalar_tac
    intro q4
    apply bind
    · apply qadd
    intro q5
    apply bind
    · apply index <;> scalar_tac
    intro q6
    apply bind
    · apply qadd
    intro q7
    apply bind
    · apply index <;> scalar_tac
    intro q8
    apply bind
    · apply qadd
    intro q9
    apply bind
    · apply index <;> scalar_tac
    intro q10
    apply bind
    · apply qadd
    intro q11
    apply bind
    · apply index <;> scalar_tac
    intro q12
    apply bind
    · apply qadd
    intro q13
    apply bind
    · apply index <;> scalar_tac
    intro q14
    apply qadd

#print axioms mask_sum_total

theorem active_block_total (selectors : reference_copy_terminal.Selectors)
    (block : Usize) (sum : aspis_core.field.QM31) (hb : block.val<64) :
    Success (reference_copy_terminal.active_block227 selectors block sum) := by
  have hlen : block.val < reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val.length := by
    rw [reference_copy_terminal.constants.ACTIVE_ROW_MASKS.property]
    exact hb
  let mask := reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val[block.val]'hlen
  have hm : MaskAllowed mask := active_masks_allowed mask (List.getElem_mem hlen)
  have hread := PV_B3P_SelectIndex227.index_value
    reference_copy_terminal.constants.ACTIVE_ROW_MASKS block hb
  unfold reference_copy_terminal.active_block227
  rw [hread]
  dsimp only
  by_cases hz : mask != 0#u16
  · simp only [show reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val[block.val]'hlen=mask from rfl,
      hz,↓reduceIte]
    apply bind
    · exact index selectors.high block hb
    intro high
    apply bind
    · exact mask_sum_total selectors.low mask hm
    intro low
    apply bind
    · exact qmul high low
    intro product
    exact qadd sum product
  · simp only [show reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val[block.val]'hlen=mask from rfl,
      hz,↓reduceIte]
    exact ok sum

#print axioms active_block_total

theorem active_loop_total (selectors : reference_copy_terminal.Selectors)
    (sum : aspis_core.field.QM31) (block : Usize) (hb : block.val≤64) :
    Success (reference_copy_terminal.Selectors.active_literal_loop selectors sum block) := by
  unfold reference_copy_terminal.Selectors.active_literal_loop
  refine loop_total _ (fun x : aspis_core.field.QM31 × Usize => 64-x.2.val)
    (fun x => x.2.val≤64) ?_ (sum,block) hb
  rintro ⟨acc,i⟩ hi
  change i.val≤64 at hi
  by_cases hp : i.val<64
  · have hb : i<64#usize := by scalar_tac
    obtain ⟨next,hnext⟩ := active_block_total selectors i acc hp
    let j := Usize.wrapping_add i 1#usize
    have hj : j.val=i.val+1 := PV_B3P_Offset226V3.add_value i 1#usize (by
      have hsize := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac)
    refine ⟨.cont (next,j),?_,?_,?_⟩
    · simp only [reference_copy_terminal.Selectors.active_literal_loop.body,hb,↓reduceIte,
        hnext,lift,bind_tc_ok,j]
    · change j.val≤64
      omega
    · change 64-j.val<64-i.val
      omega
  · have hb : ¬i<64#usize := by scalar_tac
    refine ⟨.done acc,?_,True.intro⟩
    simp only [reference_copy_terminal.Selectors.active_literal_loop.body,hb,↓reduceIte]

#print axioms active_loop_total

theorem active_total (selectors : reference_copy_terminal.Selectors) :
    Success (reference_copy_terminal.Selectors.active selectors) :=
  active_loop_total selectors aspis_core.field.QM31.ZERO 0#usize (by change 0≤64; omega)

#print axioms active_total
end PV_B3P_Success227
