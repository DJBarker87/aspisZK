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

theorem even_source (row : Usize) (hlo : 2 ≤ row.val) (hhi : row.val ≤ 8) :
    state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      () row = .ok (constantValue row 0,()) := by
  obtain ⟨sub,hsub,hsubval⟩ := AspisR1.ExtractedMaskReducerOps.sub_success row 2#usize (by simpa using hlo)
  have hmulSpec : UScalar.mul 2#usize sub ⦃z => z.val=2*sub.val⦄ := by
    apply UScalar.mul_spec
    scalar_tac
  obtain ⟨index,hmul,hindex⟩ := WP.spec_imp_exists hmulSpec
  have hidx : index.val < 14 := by rw [hindex,hsubval]; omega
  have hread := internal_source_read index hidx
  have hfin : (⟨index.val,hidx⟩ : Fin 14) = constantIndex row 0 := by
    apply Fin.ext
    unfold constantIndex
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut,
    hsub,hmul,hread,bind_tc_ok,constantValue]
  rw [hfin]

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
  have hidx : index.val < 14 := by rw [hindex,htwice,hsubval]; omega
  have hread := internal_source_read index hidx
  have hfin : (⟨index.val,hidx⟩ : Fin 14) = constantIndex row 1 := by
    apply Fin.ext
    unfold constantIndex
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut,
    hsub,hmul,hadd,hread,bind_tc_ok,constantValue]
  rw [hfin]

#print axioms weight_source
#print axioms even_source
#print axioms odd_source
end AspisR1.PoseidonInternalPairCallbacks
