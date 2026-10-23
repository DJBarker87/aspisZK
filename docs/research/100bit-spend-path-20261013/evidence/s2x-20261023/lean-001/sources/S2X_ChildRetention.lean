import AdapterRwLeadInputs

/-! Fixed owned values survive pure function application. This is NOT internal
site provenance. The existing universally quantified ChildInputRetention port
requires an additional uniqueness property that purity does not imply. -/
set_option autoImplicit false
namespace AspisR1.S2X
open Aeneas Aeneas.Std Result
open AdapterRw.LeadInputs S2LeadInterface

/-- An opaque operation has no mutable state parameter in this extraction.
Keeping the original argument alongside its result retains that exact value,
for every outcome, including errors. No assertion about native effects follows. -/
def retain {A B : Type} (f : A → B) (a : A) : A × B := (a, f a)

theorem owned_retained {A B : Type} (f : A → B) (a : A) :
    (retain f a).1 = a := rfl

/-- At fixed TX2 arguments, the extracted call cannot modify those values.
It can still choose arbitrary results; it does not produce the c-site views. -/
theorem second_owned_retained (ops : AdapterRw.Ops)
    (pub proof checkpoint : Slice U8) :
    (retain (fun args : Slice U8 × Slice U8 × Slice U8 =>
      ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        args.1 args.2.1 args.2.2 () none) (pub, proof, checkpoint)).1 =
      (pub, proof, checkpoint) := rfl

/-- Obstruction in the ACTUAL interface: the same c is quantified outside all
successful calls. If two different proofs succeed, retention at any reached
late site would identify them. Pure value semantics does not imply this. -/
theorem retention_requires_unique_second_proof (ops : AdapterRw.Ops)
    (c : Inputs Observer) (h : ChildInputRetention ops c)
    (pub1 proof1 cp1 pub2 proof2 cp2 : Slice U8)
    (ok1 : ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      pub1 proof1 cp1 () none = ok (.Ok ()))
    (ok2 : ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      pub2 proof2 cp2 () none = ok (.Ok ()))
    (s : Site) (reached : c.reached s) (late : 3 < s.rank) : proof1 = proof2 :=
  (h.second pub1 proof1 cp1 ok1 s reached late).1.symm.trans
    (h.second pub2 proof2 cp2 ok2 s reached late).1

theorem retention_obstruction (ops : AdapterRw.Ops) (c : Inputs Observer)
    (pub1 proof1 cp1 pub2 proof2 cp2 : Slice U8)
    (ok1 : ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      pub1 proof1 cp1 () none = ok (.Ok ()))
    (ok2 : ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      pub2 proof2 cp2 () none = ok (.Ok ()))
    (different : proof1 ≠ proof2) (s : Site) (reached : c.reached s)
    (late : 3 < s.rank) : ¬ ChildInputRetention ops c := by
  intro h
  exact different (retention_requires_unique_second_proof ops c h
    pub1 proof1 cp1 pub2 proof2 cp2 ok1 ok2 s reached late)

#print axioms owned_retained
#print axioms second_owned_retained
#print axioms retention_requires_unique_second_proof
#print axioms retention_obstruction
end AspisR1.S2X
