import NJA_Pow5Model

set_option autoImplicit false
noncomputable section
namespace NJA_Pow5Cut
open Aeneas Aeneas.Std Result

/-- NJA_poseidon.rs::NJA_pow5_log. Natural values decode the native u64 operands.
The three events are in source order; source association is NJA_POSEIDON_SOURCE.json.
The cut transcribes len/kind/a/b/output assertions only. Canonicality is a separate
stub-domain predicate, not an invented assertion or successful-output premise. -/
structure Event where
  kind : Nat
  a : Nat
  b : Nat
  out : U32

def Cut (x : U32) (events : Fin 3 → Event) (len : Nat) (out : U32) : Prop :=
  len = 3 ∧ (∀ r, (events r).kind = 0) ∧
  (events 0).a = x.val ∧ (events 0).b = x.val ∧
  (events 1).a = (events 0).out.val ∧ (events 1).b = (events 0).out.val ∧
  (events 2).a = (events 1).out.val ∧ (events 2).b = x.val ∧
  out = (events 2).out

def Domain (x : U32) (events : Fin 3 → Event) : Prop :=
  x.val < 2147483647 ∧ ∀ r, (events r).out.val < 2147483647

def CalleeLaws (events : Fin 3 → Event) : Prop :=
  ∀ r, (events r).out.val = ((events r).a * (events r).b) % 2147483647

theorem multiply_determined (x y reply : U32)
    (value : reply.val = (x.val*y.val)%2147483647) :
    AspisR1SemanticCallExtraction.aspis_core.field.M31.mul x y = ok reply := by
  obtain ⟨z,hz,vz,cz⟩ := NJA_FieldLaws.generated_mul x y
  have eq : z = reply := UScalar.eq_of_val_eq (vz.trans value.symm)
  simpa [eq] using hz

-- Each law acts on the SAME operands and replies the native cut recorded.
theorem compose (x : U32) (events : Fin 3 → Event) (len : Nat) (out : U32)
    (cut : Cut x events len out) (laws : CalleeLaws events) :
    NJA_FieldLaws.pow5_ref x = ok out := by
  rcases cut with ⟨hlen,hkind,a0,b0,a1,b1,a2,b2,hout⟩
  have h0 := multiply_determined x x (events 0).out (by simpa [a0,b0] using laws 0)
  have h1 := multiply_determined (events 0).out (events 0).out (events 1).out
    (by simpa [a1,b1] using laws 1)
  have h2 := multiply_determined (events 1).out x (events 2).out
    (by simpa [a2,b2] using laws 2)
  simp only [NJA_FieldLaws.pow5_ref,h0,h1,h2,bind_tc_ok,hout]

theorem reply_domains (events : Fin 3 → Event) (laws : CalleeLaws events) :
    ∀ r, (events r).out.val < 2147483647 := by
  intro r
  rw [laws r]
  exact Nat.mod_lt _ (by decide)

theorem caller_domains (x : U32) (events : Fin 3 → Event) (len : Nat) (out : U32)
    (cut : Cut x events len out) (laws : CalleeLaws events) (hx : x.val < 2147483647) :
    ∀ r, (events r).a < 2147483647 ∧ (events r).b < 2147483647 := by
  rcases cut with ⟨hlen,hkind,a0,b0,a1,b1,a2,b2,hout⟩
  have hc := reply_domains events laws
  intro r
  fin_cases r <;> simp_all

#print axioms reply_domains
#print axioms caller_domains
#print axioms multiply_determined
#print axioms compose
end NJA_Pow5Cut
end
