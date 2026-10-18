import PoseidonInternalPairSource
import PoseidonInternalStateWords

/-! Actual internal-pair callbacks, using the existing source constant reads
and checked scalar operations. Their maps only pass rows two through eight. -/
set_option autoImplicit false
namespace AspisR1.PoseidonInternalPairCallbacks
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep (State QM cell)
open AspisR1.PoseidonRemainingConstantsExact (internalConstant internal_source_read)

def weightValue (local1 : State) (row : Usize) : QM :=
  cell local1 ⟨row.val % 16,Nat.mod_lt _ (by decide)⟩

def constantIndex (row : Usize) (parity : Nat) : Fin 14 :=
  ⟨(2*(row.val-2)+parity)%14,Nat.mod_lt _ (by decide)⟩
def constantValue (row : Usize) (parity : Nat) : U32 := internalConstant (constantIndex row parity)

theorem weight_source (local1 : State) (row : Usize) (hr : row.val < 16) :
    state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      local1 row = .ok (weightValue local1 row,local1) := by
  have hread := AspisR1.PoseidonInternalStateWords.state_source_read local1 row hr
  have hfin : (⟨row.val,hr⟩ : Fin 16) = ⟨row.val%16,Nat.mod_lt _ (by decide)⟩ := by
    apply Fin.ext
    exact (Nat.mod_eq_of_lt hr).symm
  simp only [state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut,
    hread,bind_tc_ok,weightValue]
  rw [hfin]
  rfl

theorem even_source (row : Usize) (hlo : 2 ≤ row.val) (hhi : row.val ≤ 8) :
    state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      () row = .ok (constantValue row 0,()) := by
  obtain ⟨sub,hsub,hsubval⟩ := AspisR1.ExtractedMaskReducerOps.sub_success row 2#usize (by simpa using hlo)
  have hmulSpec : UScalar.mul 2#usize sub ⦃z => z.val=2*sub.val⦄ := by
    apply UScalar.mul_spec
    scalar_tac
  obtain ⟨index,hmul,hindex⟩ := WP.spec_imp_exists hmulSpec
  have htwo : (2#usize).val = 2 := by decide
  have hraw : index.val = 2 * (row.val - 2) := by
    calc
      index.val = 2 * sub.val := hindex
      _ = 2 * (row.val - 2) := by rw [hsubval, htwo]
  have hidx : index.val < 14 := by rw [hraw]; omega
  have hread := internal_source_read index hidx
  have hrawBound : 2 * (row.val - 2) < 14 := by rw [← hraw]; exact hidx
  have hfin : (⟨index.val,hidx⟩ : Fin 14) = constantIndex row 0 := by
    apply Fin.ext
    unfold constantIndex
    simp only [Nat.add_zero]
    rw [Nat.mod_eq_of_lt hrawBound]
    exact hraw
  change (do
      let i ← UScalar.sub row 2#usize
      let i1 ← UScalar.mul 2#usize i
      let i2 ← Array.index_usize poseidon2.INTERNAL i1
      ok (i2, ())) = .ok (internalConstant (constantIndex row 0), ())
  rw [hsub, bind_tc_ok, hmul, bind_tc_ok, hread, bind_tc_ok, hfin]

theorem odd_source (row : Usize) (hlo : 2 ≤ row.val) (hhi : row.val ≤ 8) :
    state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      () row = .ok (constantValue row 1,()) := by
  obtain ⟨sub,hsub,hsubval⟩ := AspisR1.ExtractedMaskReducerOps.sub_success row 2#usize (by simpa using hlo)
  have hmulSpec : UScalar.mul 2#usize sub ⦃z => z.val=2*sub.val⦄ := by
    apply UScalar.mul_spec
    scalar_tac
  obtain ⟨twice,hmul,htwice⟩ := WP.spec_imp_exists hmulSpec
  have haddSpec : UScalar.add twice 1#usize ⦃z => z.val=twice.val+1⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨index,hadd,hindex⟩ := WP.spec_imp_exists haddSpec
  have htwo : (2#usize).val = 2 := by decide
  have hone : (1#usize).val = 1 := by decide
  have hraw : index.val = 2 * (row.val - 2) + 1 := by
    calc
      index.val = twice.val + 1 := hindex
      _ = 2 * sub.val + 1 := by rw [htwice]
      _ = 2 * (row.val - 2) + 1 := by rw [hsubval, htwo]
  have hidx : index.val < 14 := by rw [hraw]; omega
  have hread := internal_source_read index hidx
  have hrawBound : 2 * (row.val - 2) + 1 < 14 := by rw [← hraw]; exact hidx
  have hfin : (⟨index.val,hidx⟩ : Fin 14) = constantIndex row 1 := by
    apply Fin.ext
    change index.val = (2 * (row.val - 2) + 1) % 14
    rw [Nat.mod_eq_of_lt hrawBound]
    exact hraw
  change (do
      let i ← UScalar.sub row 2#usize
      let i1 ← UScalar.mul 2#usize i
      let i2 ← UScalar.add i1 1#usize
      let i3 ← Array.index_usize poseidon2.INTERNAL i2
      ok (i3, ())) = .ok (internalConstant (constantIndex row 1), ())
  rw [hsub, bind_tc_ok, hmul, bind_tc_ok, hadd, bind_tc_ok, hread, bind_tc_ok, hfin]

#print axioms weight_source
#print axioms even_source
#print axioms odd_source
end AspisR1.PoseidonInternalPairCallbacks
