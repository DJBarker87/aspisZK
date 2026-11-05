import NIS_PublicCarrier
import AdapterRwCuts
set_option autoImplicit false
noncomputable section
namespace NIS_Tx1Boundary
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
abbrev AE := AdapterRw.aspis_r1_cost_probe.verifier.Error
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev APublic := NIS_PublicCarrier.APublic

/-- Exact release-only model boundary. No successful candidate outcome is
assumed. The explicit ports preserve every public field and every error. -/
def release {H : Type} (base : AspisR1CurrentCaller.Ops)
    (first : AspisR1.NHL_EmittedTx1.Prepare H)
    (D : AdapterRw.aspis_core.digest.Digest32 H) (pub : APublic)
    (public_bytes proof : Slice U8) (k : Usize) (hash : H) :
    Result (core.result.Result (alloc.vec.Vec U8) AE) :=
  NIS_PublicCarrier.resultToAdapter (AspisR1.NHL_EmittedTx1.tx1 base first
    (NIS_DigestCarrier.toCaller D) (NIS_PublicCarrier.toCaller pub)
    public_bytes proof k hash none)

/-- Candidate installation for the release None instantiation only. Other
observers retain the original slot. This does not adopt a headline dictionary. -/
def install (adapter : AdapterRw.Ops) (base : AspisR1CurrentCaller.Ops)
    (first : ∀ H : Type, AspisR1.NHL_EmittedTx1.Prepare H) : AdapterRw.Ops :=
  {adapter with op10 := fun {H} D pub public_bytes proof k hash obs =>
    match obs with
    | none => release base (first H) D pub public_bytes proof k hash
    | some callback => adapter.op10 D pub public_bytes proof k hash (some callback)}

def mapped (ops : AdapterRw.Ops) (reply : Result (core.result.Result (alloc.vec.Vec U8) AE)) :
    Result (core.result.Result (alloc.vec.Vec U8) PE) := do
  let r ← reply
  AdapterRw.core.result.Result.map_err (BuiltinFnOnce AE PE) r ops.op44

theorem digest_instance (adapter : AdapterRw.Ops) (base : AspisR1CurrentCaller.Ops)
    (first : ∀ H : Type, AspisR1.NHL_EmittedTx1.Prepare H) :
    AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (install adapter base first)=
    AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 adapter := rfl

theorem ports (adapter : AdapterRw.Ops) (base : AspisR1CurrentCaller.Ops)
    (first : ∀ H : Type, AspisR1.NHL_EmittedTx1.Prepare H) :
    @AdapterRw.Ops.op11 (install adapter base first)=@AdapterRw.Ops.op11 adapter ∧
    (install adapter base first).op43=adapter.op43 ∧
    (install adapter base first).op44=adapter.op44 := ⟨rfl,rfl,rfl⟩

theorem at_none (adapter : AdapterRw.Ops) (base : AspisR1CurrentCaller.Ops)
    (first : ∀ H : Type, AspisR1.NHL_EmittedTx1.Prepare H) {H : Type}
    (D : AdapterRw.aspis_core.digest.Digest32 H) (pub : APublic)
    (public_bytes proof : Slice U8) (k : Usize) (hash : H) :
    (install adapter base first).op10 D pub public_bytes proof k hash none=
      release base (first H) D pub public_bytes proof k hash := rfl

theorem first_decoded (adapter : AdapterRw.Ops) (base : AspisR1CurrentCaller.Ops)
    (first : ∀ H : Type, AspisR1.NHL_EmittedTx1.Prepare H)
    (pub : APublic) (public_bytes proof : Slice U8) (k : Usize) :
    AdapterRw.first_decoded (install adapter base first) pub public_bytes proof k=
      mapped adapter (release base (first Unit)
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 adapter)
        pub public_bytes proof k ()) := by
  rw [AspisR1.AdapterRw.Cuts.first_decoded_call]
  change mapped adapter (release base (first Unit)
    (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (install adapter base first))
    pub public_bytes proof k ())=_
  rw [digest_instance]

/-- The original NHL conditions are retained verbatim on the converted SAME
inputs. This is the model's law, never an asserted successful candidate reply. -/
theorem cohort (base expected : AspisR1CurrentCaller.Ops) {H : Type}
    (first : AspisR1.NHL_EmittedTx1.Prepare H)
    (D : AdapterRw.aspis_core.digest.Digest32 H) (pub : APublic)
    (public_bytes proof : Slice U8) (k : Usize) (hash : H)
    (prepare : ∀ zero, aspis_core.field.wide_exact.WideExact.ZERO base=ok zero →
      first (NIS_DigestCarrier.toCaller D) (NIS_PublicCarrier.toCaller pub) proof hash none
          (Array.repeat 29#usize zero)=
      verifier.candidate.prepare (AspisR1.NHL_Tx1Model.children base expected)
        (NIS_DigestCarrier.toCaller D) (NIS_PublicCarrier.toCaller pub) proof hash none
        (Array.repeat 29#usize zero))
    (query_loop : ∀ c, AspisR1.NHL_Tx1Model.Reaches base expected
        (NIS_DigestCarrier.toCaller D) (NIS_PublicCarrier.toCaller pub) public_bytes proof k hash c →
      base.op7 proof c.prepared c.accumulator c.scratch none c.geometry c.pending k=
      expected.op7 proof c.prepared c.accumulator c.scratch none c.geometry c.pending k)
    (checkpoint : ∀ c a pending, AspisR1.NHL_Tx1Model.Reaches base expected
        (NIS_DigestCarrier.toCaller D) (NIS_PublicCarrier.toCaller pub) public_bytes proof k hash c →
      expected.op7 proof c.prepared c.accumulator c.scratch none c.geometry c.pending k=ok (.Ok (a,pending)) →
      ∀ cells, base.op17 pending (alloc.vec.Vec.deref_mut a.weights).1=ok cells →
      base.op16 (NIS_DigestCarrier.toCaller D) c.prepared
        {a with weights:=(alloc.vec.Vec.deref_mut a.weights).2 cells} proof public_bytes hash=
      expected.op16 (NIS_DigestCarrier.toCaller D) c.prepared
        {a with weights:=(alloc.vec.Vec.deref_mut a.weights).2 cells} proof public_bytes hash) :
    release base first D pub public_bytes proof k hash=
      NIS_PublicCarrier.resultToAdapter (verifier.candidate.tx1
        (AspisR1.NHL_Tx1Model.children base expected) (NIS_DigestCarrier.toCaller D)
        (NIS_PublicCarrier.toCaller pub) public_bytes proof k hash none) := by
  exact congrArg NIS_PublicCarrier.resultToAdapter
    (AspisR1.NHL_Tx1Model.source base expected first (NIS_DigestCarrier.toCaller D)
      (NIS_PublicCarrier.toCaller pub) public_bytes proof k hash prepare query_loop checkpoint)

theorem abort_prefix (ops : AdapterRw.Ops) (error : Error) :
    mapped ops (.fail error)=.fail error ∧ mapped ops .div=.div := ⟨rfl,rfl⟩

#print axioms digest_instance
#print axioms ports
#print axioms at_none
#print axioms first_decoded
#print axioms cohort
#print axioms abort_prefix
end NIS_Tx1Boundary
