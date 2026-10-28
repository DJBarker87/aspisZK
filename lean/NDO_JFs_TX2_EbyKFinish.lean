import RPu_JFs_TX2_DotFinish
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_EbyKFinish
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
theorem source (s : FIo_Native.fast_pairing.EbyKDot) :
    ∃ out, FIo_Native.fast_pairing.EbyKDot.finish s=ok out ∧ FIo_WideValues.Canon out := by
  obtain ⟨a,ha,ca⟩ := JFs_TX2_DotFinish.source s.c0
  obtain ⟨b,hb,cb⟩ := JFs_TX2_DotFinish.source s.c1
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at ha ca
  rw [eb] at hb cb
  simp only [JFs_TX2_DotFinish.Canon,pack,Array.make,List.mem_cons,List.not_mem_nil,
    IsEmpty.forall_iff,forall_const,forall_eq_or_imp,and_true] at ca cb
  have r0 : Array.index_usize (pack a0 a1 a2 a3) 0#usize=ok a0 := rfl
  have r1 : Array.index_usize (pack a0 a1 a2 a3) 1#usize=ok a1 := rfl
  have r2 : Array.index_usize (pack a0 a1 a2 a3) 2#usize=ok a2 := rfl
  have r3 : Array.index_usize (pack a0 a1 a2 a3) 3#usize=ok a3 := rfl
  have r4 : Array.index_usize (pack a4 a5 a6 a7) 0#usize=ok a4 := rfl
  have r5 : Array.index_usize (pack a4 a5 a6 a7) 1#usize=ok a5 := rfl
  have r6 : Array.index_usize (pack a4 a5 a6 a7) 2#usize=ok a6 := rfl
  have r7 : Array.index_usize (pack a4 a5 a6 a7) 3#usize=ok a7 := rfl
  obtain ⟨out,run,canon⟩ := JFs_TX2_FromLimbs.packed a0 a1 a2 a3 a4 a5 a6 a7
    ⟨ca.1,ca.2.1,ca.2.2.1,ca.2.2.2,cb.1,cb.2.1,cb.2.2.1,cb.2.2.2⟩
  refine ⟨out,?_,canon⟩
  simp only [FIo_Native.fast_pairing.EbyKDot.finish,ha,hb,bind_tc_ok,
    FIo_Native.fast_pairing.canonical.Q.limbs,r0,r1,r2,r3,r4,r5,r6,r7]
  change (do let o ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
               (JFs_TX2_Eight.pack a0 a1 a2 a3 a4 a5 a6 a7)
             core.option.Option.unwrap o)=ok out
  rw [run]
  rfl

#print axioms source
end AspisR1.JFs_TX2_EbyKFinish
end
