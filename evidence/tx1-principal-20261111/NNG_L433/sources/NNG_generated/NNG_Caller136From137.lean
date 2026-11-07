import NNG_Data137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Caller136From137
open NNG_Data137

theorem fallback_exact (a : Args) (env : RSL.Env) (p : LIB_VCarriers.Prefix) (t0 : LIB_VCarriers.Transcript)
    (c : LIB_VCarriers.Challenges) (t1 : LIB_VCarriers.Transcript)
    (parsed : LIB_VParsePrefix.eval a.bytes=.ok p)
    (transcripted : LIB_VPublicTranscript.eval (a.public_,LIB_VCarriers.c1Root p) env=.ok t0)
    (begun : LIB_VBegin.eval (p,t0) env=.ok (c,t1)) : fallback a env=c.eta := by
  simp only [fallback,parsed,transcripted,begun]
#print axioms fallback_exact

/-- The exact canonical child-domain clause is derived on the SAME reached
parse/public/begin arms. It is not an extra137 caller or success premise. -/
theorem finish_domain (a : Args) (env : RSL.Env) (domain : RSL.TX1_137.Domain VL a)
    (p : LIB_VCarriers.Prefix) (t0 : LIB_VCarriers.Transcript)
    (c : LIB_VCarriers.Challenges) (t1 : LIB_VCarriers.Transcript)
    (parsed : LIB_VParsePrefix.eval a.bytes=.ok p)
    (transcripted : LIB_VPublicTranscript.eval (a.public_,LIB_VCarriers.c1Root p) env=.ok t0)
    (begun : LIB_VBegin.eval (p,t0) env=.ok (c,t1)) : RSL.TX1_136.Domain VL ⟨a.public_,p,t1,c⟩ := by
  have caller := LIB_VDomains.finish_of_eval a.public_ a.bytes env domain.1 domain.2
  rw [parsed,transcripted,begun] at caller
  exact caller
#print axioms finish_domain
end AspisR1.NNG_Caller136From137
