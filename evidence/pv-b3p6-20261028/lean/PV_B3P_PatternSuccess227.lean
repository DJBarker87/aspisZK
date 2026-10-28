import PV_B3P_PowersSuccess227
import PV_B3P_PatternBounds227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem widen_u8 (x : U8) : (core.convert.num.FromUsizeU8.from x).val=x.val := by
  change (UScalar.cast .Usize x).val=x.val
  simp only [UScalar.cast_val_eq,UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> scalar_tac

theorem pattern_limb_total (pattern : reference_copy_terminal.CompiledPoolV1PairForestPattern)
    (limb : Usize) (openings powers : Array aspis_core.field.QM31 16#usize)
    (value : aspis_core.field.QM31) (hp : PatternSafe pattern) (hl : limb.val<16) :
    Success (reference_copy_terminal.pattern_limb227 pattern limb openings powers value) := by
  have hk := PV_B3P_SelectIndex227.index_value pattern.kinds limb hl
  have hc := PV_B3P_SelectIndex227.index_value pattern.columns limb hl
  let col := pattern.columns.val[limb.val]'(by rw [pattern.columns.property]; exact hl)
  have hcol : col.val<16 := hp col (List.getElem_mem _)
  unfold reference_copy_terminal.pattern_limb227
  rw [hk]
  dsimp only
  by_cases hb : pattern.kinds.val[limb.val]'(by rw [pattern.kinds.property]; exact hl)=1#u8
  · simp only [hb,↓reduceIte]
    rw [hc]
    simp only [lift,bind_tc_ok]
    apply bind
    · apply index
      rw [widen_u8]
      exact hcol
    intro opening
    apply bind
    · exact index pattern.offsets limb hl
    intro offset
    apply bind
    · exact ⟨_,rfl⟩
    intro lifted
    apply bind
    · exact qadd opening lifted
    intro source
    apply bind
    · exact index powers limb hl
    intro power
    apply bind
    · exact qmul power source
    intro term
    exact qadd value term
  · simp only [hb,↓reduceIte]
    exact ok value

#print axioms widen_u8
#print axioms pattern_limb_total

theorem pattern_inner_total (openings powers : Array aspis_core.field.QM31 16#usize)
    (limb : Usize) (pattern : reference_copy_terminal.CompiledPoolV1PairForestPattern)
    (value : aspis_core.field.QM31) (hp : PatternSafe pattern) (hl : limb.val≤16) :
    Success (reference_copy_terminal.pattern_values_literal_loop1_loop0 openings powers limb pattern value) := by
  have hw : aspis_statement.poseidon2.POSEIDON2_WIDTH=16#usize := by
    unfold aspis_statement.poseidon2.POSEIDON2_WIDTH
    rfl
  unfold reference_copy_terminal.pattern_values_literal_loop1_loop0
  refine loop_total _ (fun x : Usize × aspis_core.field.QM31 => 16-x.1.val)
    (fun x => x.1.val≤16) ?_ (limb,value) hl
  rintro ⟨i,acc⟩ hi
  change i.val≤16 at hi
  by_cases hlt : i.val<16
  · have hb : i<16#usize := by scalar_tac
    obtain ⟨next,hnext⟩ := pattern_limb_total pattern i openings powers acc hp hlt
    let j := Usize.wrapping_add i 1#usize
    have hj : j.val=i.val+1 := PV_B3P_Offset226V3.add_value i 1#usize (by
      have hsize := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac)
    refine ⟨.cont (j,next),?_,?_,?_⟩
    · simp only [reference_copy_terminal.pattern_values_literal_loop1_loop0.body,hw,hb,↓reduceIte,
        hnext,lift,bind_tc_ok,j]
    · change j.val≤16
      omega
    · change 16-j.val<16-i.val
      omega
  · have hb : ¬i<16#usize := by scalar_tac
    refine ⟨.done (i,acc),?_,True.intro⟩
    simp only [reference_copy_terminal.pattern_values_literal_loop1_loop0.body,hw,hb,↓reduceIte]

#print axioms pattern_inner_total

theorem pattern_outer_total (openings powers : Array aspis_core.field.QM31 16#usize)
    (limb : Usize) (result : Array aspis_core.field.QM31 14#usize)
    (pattern_index : Usize) (hi : pattern_index.val≤14) :
    Success (reference_copy_terminal.pattern_values_literal_loop1 openings powers limb result pattern_index) := by
  have hw : reference_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1=14#usize := by
    unfold reference_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1
    rfl
  unfold reference_copy_terminal.pattern_values_literal_loop1
  refine loop_total _ (fun x : Usize × Array aspis_core.field.QM31 14#usize × Usize => 14-x.2.2.val)
    (fun x => x.2.2.val≤14) ?_ (limb,result,pattern_index) hi
  rintro ⟨oldlimb,values,i⟩ hi
  change i.val≤14 at hi
  by_cases hlt : i.val<14
  · have hb : i<14#usize := by scalar_tac
    have hlen : i.val<reference_copy_terminal.constants.COPY_PATTERNS.val.length := by
      rw [reference_copy_terminal.constants.COPY_PATTERNS.property]
      exact hlt
    let pattern := reference_copy_terminal.constants.COPY_PATTERNS.val[i.val]'hlen
    have hpat := PV_B3P_SelectIndex227.index_value reference_copy_terminal.constants.COPY_PATTERNS i hlt
    have hsafe : PatternSafe pattern := patterns_safe pattern (List.getElem_mem hlen)
    obtain ⟨⟨limb1,value⟩,hvalue⟩ := pattern_inner_total openings powers 0#usize pattern
      aspis_core.field.QM31.ZERO hsafe (by change 0≤16; omega)
    obtain ⟨values1,hvalues1⟩ := update values i value hlt
    let j := Usize.wrapping_add i 1#usize
    have hj : j.val=i.val+1 := PV_B3P_Offset226V3.add_value i 1#usize (by
      have hsize := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac)
    refine ⟨.cont (limb1,values1,j),?_,?_,?_⟩
    · simp only [reference_copy_terminal.pattern_values_literal_loop1.body,hw,hb,↓reduceIte,
        hpat,hvalue,hvalues1,lift,bind_tc_ok,j]
    · change j.val≤14
      omega
    · change 14-j.val<14-i.val
      omega
  · have hb : ¬i<14#usize := by scalar_tac
    refine ⟨.done values,?_,True.intro⟩
    simp only [reference_copy_terminal.pattern_values_literal_loop1.body,hw,hb,↓reduceIte]

#print axioms pattern_outer_total

theorem patterns_total (openings : Array aspis_core.field.QM31 16#usize)
    (lambda : aspis_core.field.QM31) :
    Success (reference_copy_terminal.pattern_values openings lambda) := by
  unfold reference_copy_terminal.pattern_values reference_copy_terminal.pattern_values_literal
  apply bind
  · exact pattern_powers_total lambda _ lambda 0#usize (by change 0≤16; omega)
  rintro ⟨powers,limb⟩
  exact pattern_outer_total openings powers limb _ 0#usize (by change 0≤14; omega)

#print axioms patterns_total
end PV_B3P_Success227
