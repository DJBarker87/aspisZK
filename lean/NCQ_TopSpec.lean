import S2W_DigestExtraction
import S2W_D189Wrappers

/-! Result-only specification audit. No Rust semantics, certificates or trust
adoption are encoded here. The factorization is equivalent to the old premise,
not a proof that a concrete native entry satisfies it. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCQ_TopSpec
open Aeneas Aeneas.Std Result S2W_ExtractionBoundary

abbrev Hash := S2Z.Oracle.Parts → Result S2Z.Oracle.Digest
abbrev DigestFn := AdapterRw.SolanaDigest → Hash

/-- The three full-domain fields, with no accepted-run guard. -/
theorem fields_iff (ops : AdapterRw.Ops) (native1 : First) (native2 : Second)
    (hashv : Hash) :
    S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv ↔
    (∀ program accounts data, native1 program accounts data =
      AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data) ∧
    (∀ program accounts data slot, native2 program accounts data slot =
      AdapterRw.r1_pool_adapter.owned.stage2_owned ops program accounts data slot) ∧
    (∀ self parts, ops.op43 self parts = S2W_DigestExtraction.digest hashv self parts) := by
  constructor
  · intro h
    exact ⟨h.stage1, h.stage2, h.digestSource⟩
  · rintro ⟨first, second, digest⟩
    exact ⟨first, second, digest⟩

/-- A prospective extracted reference must be proved to equal this exact SDK.
These are model-side obligations; no such reference implementation is supplied. -/
structure ReferenceModel (ops : AdapterRw.Ops) (hashv : Hash)
    (ref1 : First) (ref2 : Second) (refDigest : DigestFn) : Prop where
  stage1 : ref1 = AdapterRw.r1_pool_adapter.owned.stage1_owned ops
  stage2 : ref2 = AdapterRw.r1_pool_adapter.owned.stage2_owned ops
  digest : refDigest = S2W_DigestExtraction.digest hashv

/-- Result projection of the residual semantic link. This is explicitly a
hypothesis, not a Kani verdict and not a new logical axiom. -/
structure SemanticLink (ops : AdapterRw.Ops) (native1 : First) (native2 : Second)
    (ref1 : First) (ref2 : Second) (refDigest : DigestFn) : Prop where
  stage1 : native1 = ref1
  stage2 : native2 = ref2
  digest : ops.op43 = refDigest

/-- Conditional assembly: certifying these hypotheses externally is necessary. -/
theorem assemble (ops : AdapterRw.Ops) (native1 : First) (native2 : Second)
    (hashv : Hash) (ref1 : First) (ref2 : Second) (refDigest : DigestFn)
    (model : ReferenceModel ops hashv ref1 ref2 refDigest)
    (link : SemanticLink ops native1 native2 ref1 ref2 refDigest) :
    S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv := by
  refine ⟨?_, ?_, ?_⟩
  · intro program accounts data
    exact congrFun (congrFun (congrFun (link.stage1.trans model.stage1) program) accounts) data
  · intro program accounts data slot
    exact congrFun (congrFun (congrFun (congrFun
      (link.stage2.trans model.stage2) program) accounts) data) slot
  · intro self parts
    exact congrFun (congrFun (link.digest.trans model.digest) self) parts

/-- This equivalence prevents a premise-removal claim from mere repackaging. -/
theorem factor_iff (ops : AdapterRw.Ops) (native1 : First) (native2 : Second)
    (hashv : Hash) :
    S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv ↔
    ∃ ref1 ref2 refDigest,
      ReferenceModel ops hashv ref1 ref2 refDigest ∧
      SemanticLink ops native1 native2 ref1 ref2 refDigest := by
  constructor
  · intro h
    refine ⟨AdapterRw.r1_pool_adapter.owned.stage1_owned ops,
      AdapterRw.r1_pool_adapter.owned.stage2_owned ops,
      S2W_DigestExtraction.digest hashv, ⟨rfl, rfl, rfl⟩, ?_⟩
    exact ⟨funext (fun p => funext (fun a => funext (fun d => h.stage1 p a d))),
      funext (fun p => funext (fun a => funext (fun d => funext (fun s => h.stage2 p a d s)))),
      funext (fun self => funext (fun parts => h.digestSource self parts))⟩
  · rintro ⟨ref1, ref2, refDigest, model, link⟩
    exact assemble ops native1 native2 hashv ref1 ref2 refDigest model link

/-- The digest condition is exact equality to hashv, without a success premise. -/
theorem digest_source_iff (ops : AdapterRw.Ops) (hashv : Hash) :
    (∀ self parts, ops.op43 self parts = S2W_DigestExtraction.digest hashv self parts) ↔
    (∀ self parts, ops.op43 self parts = hashv parts) := by
  constructor
  · intro h self parts
    exact (h self parts).trans (S2W_DigestExtraction.digest_eq_hashv hashv self parts)
  · intro h self parts
    exact (h self parts).trans (S2W_DigestExtraction.digest_eq_hashv hashv self parts).symm

/-- Definitional stage identities only for model-instantiated native values.
The digest premise is retained; no association with Rust is claimed. -/
theorem model_instance (ops : AdapterRw.Ops) (hashv : Hash)
    (digest : ∀ self parts, ops.op43 self parts = hashv parts) :
    S2W_DigestExtraction.AeneasExtraction ops
      (AdapterRw.r1_pool_adapter.owned.stage1_owned ops)
      (AdapterRw.r1_pool_adapter.owned.stage2_owned ops) hashv := by
  exact ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, (digest_source_iff ops hashv).mpr digest⟩

#print axioms fields_iff
#print axioms assemble
#print axioms factor_iff
#print axioms digest_source_iff
#print axioms model_instance
#print First
#print Second
#print S2W_DigestExtraction.AeneasExtraction
#print P1
#print RuntimeSyscall
#print S2Z.Oracle.RuntimeSyscall
#print S2Z.Oracle.P1Realization
#print S2W_D189Wrappers.first
#print S2W_D189Wrappers.second
end AspisR1.NCQ_TopSpec
end
