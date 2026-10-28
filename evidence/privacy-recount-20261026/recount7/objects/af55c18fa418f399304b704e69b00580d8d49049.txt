import R1Z.PV_RunJoin_IndexedTarget19
set_option autoImplicit false
namespace R1Z.PV_RunJoin_IndexedPair19
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

theorem source (s pre first second : State) (n : Usize) (hn : n.val < 11)
    (hp : (if n = 0#usize then poseidon2.external_linear_lazy s else ok s) = ok pre)
    (hf : poseidon2.apply_round_by_index pre (Usize.wrapping_mul 2#usize n) = ok (some (),first))
    (hs : poseidon2.apply_round_by_index first
      (Usize.wrapping_add (Usize.wrapping_mul 2#usize n) 1#usize) = ok (some (),second)) :
    poseidon2.evaluate_trace_round_pair s n = ok (some (first,second)) := by
  have hd : poseidon2.POSEIDON2_ROUNDS / 2#usize = ok 11#usize := by
    rw [poseidon2.POSEIDON2_ROUNDS]
    obtain ⟨q,hq,hv⟩ := UScalar.div_spec 22#usize (y := 2#usize) (by simp)
    have he : q = 11#usize := by
      apply UScalar.eq_of_val_eq
      simpa using hv
    simpa only [he] using hq
  rw [poseidon2.evaluate_trace_round_pair,hd]
  simp only [bind_tc_ok]
  rw [if_neg (by simpa [UScalar.le_equiv] using (show ¬ 11 ≤ n.val by omega))]
  by_cases hz : n = 0#usize
  · rw [if_pos hz] at hp ⊢
    rw [hp]
    simp only [bind_tc_ok,lift,hf,hs,core.option.Option.Insts.CoreOpsTry_traitTry.branch,BuilderForestStd.branch]
  · rw [if_neg hz] at hp ⊢
    have he : s = pre := Result.ok.inj hp
    subst pre
    simp only [bind_tc_ok,lift,hf,hs,core.option.Option.Insts.CoreOpsTry_traitTry.branch,BuilderForestStd.branch]
#print axioms source
end R1Z.PV_RunJoin_IndexedPair19
