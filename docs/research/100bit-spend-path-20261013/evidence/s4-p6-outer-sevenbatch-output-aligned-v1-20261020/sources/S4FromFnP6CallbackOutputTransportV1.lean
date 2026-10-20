import S4FromFnP6CallbackOutputLinkV1
import StepByScheduleV3

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FromFnP6Generated

theorem generatedCallback_success_output_transport
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (q : Aeneas.Std.Array Std.U8 608#usize)
    (g : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) {value : aspis_core.field.wide_exact.WideExact}
    {c' : fast_dots.four_dots.closure}
    (hcall : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops) (q,g) slot = .ok (value,c')) :
    ∃ limbs : Aeneas.Std.Array Std.U64 8#usize,
      ∃ vals : Aeneas.Std.Array Std.U32 8#usize,
        ∃ optValue : Option aspis_core.field.wide_exact.WideExact,
          ∃ bodyValue tailValue : aspis_core.field.wide_exact.WideExact,
            fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
              (fourDotsOpsWithP6ArrayFromFnN4N8 ops)
              AspisR1FastDotsStepSchedule.startBy q g slot (Array.repeat 8#usize 0#u64) = .ok limbs ∧
            (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
              (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
                (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs = .ok vals ∧
            (fourDotsOpsWithP6ArrayFromFnN4N8 ops).wideFromLimbs vals = .ok optValue ∧
            core.option.Option.unwrap optValue = .ok bodyValue ∧
            (fourDotsOpsWithP6ArrayFromFnN4N8 ops).wideAdd bodyValue tailValue = .ok value := by
  obtain ⟨a,g',iter,limbs,vals,optValue,bodyValue,tailValue,hc,hstep,hloop,harray,
      hwide,hunwrap,hadd⟩ := generatedCallback_success_output_link ops (q,g) slot hcall
  rcases Prod.mk.inj hc with ⟨rfl,rfl⟩
  have hstart : iter = AspisR1FastDotsStepSchedule.startBy :=
    Result.ok.inj (hstep.symm.trans AspisR1FastDotsStepSchedule.initialized_step_by)
  have hloop' : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops)
      AspisR1FastDotsStepSchedule.startBy q g slot (Array.repeat 8#usize 0#u64) = .ok limbs := by
    simpa only [hstart] using hloop
  exact ⟨limbs,vals,optValue,bodyValue,tailValue,hloop',harray,hwide,hunwrap,hadd⟩

#print axioms generatedCallback_success_output_transport
end AspisR1FromFnP6Generated
