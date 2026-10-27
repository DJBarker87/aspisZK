import R1Z.PV_B2_RawSamplerFuns
import R1Z.PV_B2_Sampler
set_option autoImplicit false
noncomputable section
namespace PV_B2_SamplerCarrier
open Aeneas Aeneas.Std Result
abbrev Raw := PV_B2_249.aspis_core.field.wide_exact.WideExact
abbrev Native := ProverRwFull.aspis_core.field.wide_exact.WideExact

def toNative (v : Raw) : Native :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
   ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩
def fromNative (v : Native) : Raw :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
   ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩
def mapResult {α β : Type} (f : α → β) : Result α → Result β
  | .ok v => .ok (f v)
  | .fail e => .fail e
  | .div => .div

theorem roundtrip (v : Native) : toNative (fromNative v) = v := by cases v; rfl
theorem roundtrip_raw (v : Raw) : fromNative (toNative v) = v := by cases v; rfl

/-- A field-for-field carrier change preserves both failure tags and divergence. -/
theorem map_bind {α β γ : Type} (f : β → γ) (x : Result α) (k : α → Result β) :
    mapResult f (x >>= k) = (x >>= fun a => mapResult f (k a)) := by cases x <;> rfl

#print axioms roundtrip
#print axioms roundtrip_raw
#print axioms map_bind
end PV_B2_SamplerCarrier
