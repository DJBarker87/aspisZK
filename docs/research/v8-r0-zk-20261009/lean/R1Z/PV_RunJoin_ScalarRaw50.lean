import R1Z.PV_RunJoin_SemanticScalar50
import R1Z.PV_RunJoin_SamplerValue49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ScalarRaw50
open Aeneas Aeneas.Std ProverRwFull
open ProverCommitWideOps48

def raw (x : aspis_core.field.wide_exact.WideExact) : Raw :=
  (PV_RunJoin_SemanticScalar50.raw x.c0,PV_RunJoin_SemanticScalar50.raw x.c1)

theorem roundtrip (a : Raw) : raw (ProverRwDictionaryTower.fromW (source a))=a := by
  rcases a with ⟨a,b⟩
  apply Prod.ext <;> exact PV_RunJoin_SemanticScalar50.roundtrip _

theorem injective : Function.Injective (fun a : Raw => ProverRwDictionaryTower.fromW (source a)) := by
  intro a b h
  have hr := congrArg raw h
  simpa only [roundtrip] using hr
#print axioms raw
#print axioms roundtrip
#print axioms injective
end R1Z.PV_RunJoin_ScalarRaw50
