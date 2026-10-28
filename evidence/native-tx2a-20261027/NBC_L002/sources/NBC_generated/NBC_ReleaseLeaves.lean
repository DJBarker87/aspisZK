import AdapterRwModel
import CurrentCompactCallerModelV1
import CurrentClaimSumModel
set_option autoImplicit false
noncomputable section
namespace NBC_ReleaseLeaves
open Aeneas Aeneas.Std Result

/-- Every release caller obtains precisely None; no observer hypothesis. -/
theorem observer (ops : AdapterRw.Ops) : AdapterRw.observer ops = ok none := rfl

/-- Release mark has no callback and no effect, for every actual phase. -/
theorem mark (phase : AspisR1CurrentCaller.verifier.Phase) :
    AspisR1CurrentCaller.verifier.mark none phase = ok () := rfl

/-- The retained release trace definition ignores all of its arguments. -/
theorem value (tag : U16) (index : Usize)
    (x : AspisR1CurrentPreparedClaim.aspis_core.field.WideExact) :
    AspisR1CurrentPreparedClaim.trace.value tag index x = ok () := rfl

abbrev Parts := Slice (Slice U8)
abbrev Digest := Array U8 32#usize

/-- The exact emitted to_bytes body; the hash value is an arbitrary reply. -/
def toBytes (digest : Digest) : Result Digest := ok digest

/-- Frozen three-line source wrapper, with only the runtime hashv call external. -/
def sourceDigest (hashv : Parts → Result Digest) (_self : AdapterRw.SolanaDigest)
    (parts : Parts) : Result Digest := do
  let digest ← hashv parts
  toBytes digest

/-- All Result paths and the SAME ordered parts are preserved. -/
theorem digest_result (hashv : Parts → Result Digest)
    (self : AdapterRw.SolanaDigest) (parts : Parts) :
    sourceDigest hashv self parts = hashv parts := by
  cases h : hashv parts <;> simp only [sourceDigest, h, toBytes,
    bind_tc_ok, bind_tc_fail, bind_tc_div]

/-- Local dictionary installation only. This does not identify the adopted
headline dictionary with the concrete source wrapper. -/
def digestOps (ops : AdapterRw.Ops) (hashv : Parts → Result Digest) : AdapterRw.Ops :=
  {ops with op43 := sourceDigest hashv}

theorem digest_installed (ops : AdapterRw.Ops) (hashv : Parts → Result Digest)
    (self : AdapterRw.SolanaDigest) (parts : Parts) :
    (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (digestOps ops hashv)).digest self parts =
      hashv parts := digest_result hashv self parts

/-- Program error VALUE port only. The actual msg! runtime effect is retained
as an open native obligation; enum conversions in NBI2 are not this wrapper. -/
def errorValue (_e : AdapterRw.aspis_r1_cost_probe.verifier.Error) :
    Result AdapterRw.solana_program_error.ProgramError :=
  ok .InvalidInstructionData

def errorOps (ops : AdapterRw.Ops) : AdapterRw.Ops := {ops with op44 := errorValue}

theorem error_installed (ops : AdapterRw.Ops)
    (e : AdapterRw.aspis_r1_cost_probe.verifier.Error) :
    (errorOps ops).op44 e = ok .InvalidInstructionData := rfl

#print axioms observer
#print axioms mark
#print axioms value
#print axioms digest_result
#print axioms digest_installed
#print axioms error_installed
end NBC_ReleaseLeaves
