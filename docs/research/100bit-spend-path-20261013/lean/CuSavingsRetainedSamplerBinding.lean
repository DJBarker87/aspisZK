import AspisR1RhoPrepared.Funs
import CuSavingsCanonicalDotsSources
import CuSavingsLibraOrigins
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedSamplerBinding
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
abbrev E := aspis_core.field.WideExact
abbrev S := AspisR1CanonicalSampler.field.wide_exact.WideExact
abbrev I := AspisR1CanonicalInputs.field.wide_exact.WideExact

def digest {H : Type} (d : aspis_core.Digest32 H) : AspisR1CanonicalSampler.Digest32 H :=
  ⟨d.coremarkerCopyInst,d.digest⟩
def transcript {H : Type} (t : transcript.Transcript H) : AspisR1CanonicalSampler.transcript.Transcript H := ⟨t.state,t.hash⟩
def fromTranscript {H : Type} (t : AspisR1CanonicalSampler.transcript.Transcript H) : transcript.Transcript H := ⟨t.state,t.hash⟩
def fromSample (x : S) : E :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def input (x : E) : I :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def fromInput (x : I) : E :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def libra (x : E) : CuSavingsLibraConcrete.L.E :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def table {N : Usize} (xs : Array I N) : Array E N :=
  ⟨xs.val.map fromInput,by simp only [List.length_map,xs.property]⟩
variable [AspisR1CanonicalSampler.Shared]
def scalar {H : Type} (d : aspis_core.Digest32 H) (t : transcript.Transcript H)
    (row : U8) (payload : Slice U8) (nonzero : Bool) : Result (E × transcript.Transcript H) := do
  let (value,after) ← AspisR1CanonicalSampler.transcript.Transcript.scalar (digest d) (transcript t) row payload nonzero
  .ok (fromSample value,fromTranscript after)
def powers (N : Usize) (value : E) : Result (Array E N) := do
  let xs ← AspisR1CanonicalInputs.weights.powers N (input value)
  .ok (table xs)
@[reducible] def binding (common : PreparedCommon) : PreparedCommon :=
  {common with scalar := scalar, powers := powers}

private theorem bind_ok {A B : Type} (m : Result A) (k : A→Result B) (out : B)
    (h : (m >>= k)=.ok out) : ∃ x,m=.ok x ∧ k x=.ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

variable [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalKReader.Runtime]
theorem scalar_origins {H : Type} (d : aspis_core.Digest32 H) (t after : transcript.Transcript H)
    (row : U8) (payload : Slice U8) (nonzero : Bool) (value : E)
    (h : scalar d t row payload nonzero=.ok (value,after)) :
    CuSavingsCanonicalDotsSources.SourceValue (input value) ∧
      (nonzero=false → CuSavingsLibraOrigins.Alpha (libra value)) := by
  unfold scalar at h
  obtain ⟨⟨sample,finalT⟩,hs,h⟩ := bind_ok _ _ _ h
  simp only [uncurry_apply_pair] at h
  have he := Result.ok.inj h
  have hv := congrArg Prod.fst he
  change fromSample sample=value at hv
  subst value
  constructor
  · exact CuSavingsCanonicalDotsSources.SourceValue.sampled (digest d) (transcript t) finalT row payload nonzero sample hs
  · intro hn
    subst nonzero
    exact CuSavingsLibraOrigins.Alpha.sampled (digest d) (transcript t) finalT row payload sample hs

theorem powers_source (N : Usize) (value : E) (xs : Array E N)
    (h : powers N value=.ok xs) :
    ∃ source,AspisR1CanonicalInputs.weights.powers N (input value)=.ok source ∧ xs=table source := by
  unfold powers at h
  obtain ⟨source,hs,h⟩ := bind_ok _ _ _ h
  exact ⟨source,hs,(Result.ok.inj h).symm⟩

#print axioms scalar_origins
#print axioms powers_source
#print axioms binding
end AspisR1.CuSavingsRetainedSamplerBinding
