import PV_B3P_ClaimSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem carry_loop_total (initial : U64) (carry : Usize) (hc : carry.val≤20) :
    Success (reference_terminal.bounded_append_carry_loop initial carry) := by
  unfold reference_terminal.bounded_append_carry_loop
  refine loop_total _ (fun x : U64 × Usize => 20-x.2.val)
    (fun x => x.2.val≤20) ?_ (initial,carry) hc
  rintro ⟨index,i⟩ hbound
  change i.val≤20 at hbound
  by_cases hp : i.val<20
  · have hb : i<20#usize := by scalar_tac
    by_cases bit : index &&& 1#u64 = 0#u64
    · refine ⟨.done (i,some i),?_,True.intro⟩
      simp only [reference_terminal.bounded_append_carry_loop.body,hb,bit,
        ↓reduceIte,lift,bind_tc_ok]
    · let next := Usize.wrapping_add i 1#usize
      have hn : next.val=i.val+1 := PV_B3P_Offset226V3.add_value i 1#usize
        (by have hsize := usize_1024_size; change i.val+1 < _; omega)
      refine ⟨.cont (U64.wrapping_shr index 1#u32,next),?_,?_,?_⟩
      · simp only [reference_terminal.bounded_append_carry_loop.body,hb,bit,
          ↓reduceIte,lift,bind_tc_ok,next]
      · change next.val≤20
        omega
      · change 20-next.val<20-i.val
        omega
  · have hb : ¬i<20#usize := by scalar_tac
    refine ⟨.done (i,none),?_,True.intro⟩
    simp only [reference_terminal.bounded_append_carry_loop.body,hb,↓reduceIte]

theorem carry_total (index : U64) : Success (reference_terminal.bounded_append_carry index) := by
  unfold reference_terminal.bounded_append_carry
  apply bind
  · exact carry_loop_total index 0#usize (by change 0≤20; omega)
  rintro ⟨carry,pending⟩
  cases pending <;> exact ok _

#print axioms carry_loop_total
#print axioms carry_total
end PV_B3P_Success227
