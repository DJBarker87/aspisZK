import R1Z.ProverRwDictionaryMerkle
import R1Z.ProverCommitPolicies25
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionarySamplers
open Aeneas Aeneas.Std Result ProverRwFull
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev P := ProverCommitPolicies25.E

def fromPolicy (v : P) : W :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
   ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩
def toPolicy (v : W) : P :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
   ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩
theorem roundtrip (v : P) : toPolicy (fromPolicy v) = v := by cases v; rfl

def gamma (block : Array U8 32#usize) : Result W := do
  let v ← ProverCommitPolicies25.gamma block
  .ok (fromPolicy v)
def ordinary (block : Array U8 32#usize) : Result W := do
  let v ← ProverCommitPolicies25.ordinary block
  .ok (fromPolicy v)
def decode (v : W) := ProverCommitPolicies25.decode (toPolicy v)

variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwDictionaryMerkle.selected ops with op249 := gamma,op250 := ordinary}

theorem gamma_installed (ops : ExternalFuns) (block : Array U8 32#usize) :
    (selected ops).op249 block = gamma block := rfl
theorem ordinary_installed (ops : ExternalFuns) (block : Array U8 32#usize) :
    (selected ops).op250 block = ordinary block := rfl

/-- Total retained ordinary sampler with its exact field rank, for every block.
This is a source-policy installation, not a native entropy law or native
checked/wrapping traversal association. -/
theorem ordinary_rank (ops : ExternalFuns) (block : Array U8 32#usize) :
    ∃ v, (selected ops).op250 block = .ok v ∧
      decode v = R0C.ModuloField.fieldRank
        ⟨AspisR1.SourceSamplerByteRank.rank block % AspisCircleGroupOrder.P^8,
          Nat.mod_lt _ (Nat.pow_pos (by decide))⟩ := by
  obtain ⟨v,hv,hd⟩ := ProverCommitPolicies25.ordinary_total (fun _ _ => .fail .panic) block
  refine ⟨fromPolicy v,?_,?_⟩
  · change (do let v ← ProverCommitPolicies25.ordinary block; .ok (fromPolicy v)) = _
    change ProverCommitPolicies25.ordinary block = .ok v at hv
    rw [hv]
    rfl
  · simpa only [decode,roundtrip] using hd

theorem gamma_rank (ops : ExternalFuns) (block : Array U8 32#usize) :
    ∃ v, (selected ops).op249 block = .ok v ∧
      ∃ scalar : Fin (AspisCircleGroupOrder.P^8),
        scalar.val = AspisR1.SourceSamplerByteRank.rank block %
          (AspisCircleGroupOrder.P^8-1)+1 ∧
        decode v = R0C.ModuloField.fieldRank scalar := by
  obtain ⟨v,hv,scalar,hs,hd⟩ := ProverCommitPolicies25.gamma_rank (fun _ _ => .fail .panic) block
  refine ⟨fromPolicy v,?_,scalar,hs,?_⟩
  · change (do let v ← ProverCommitPolicies25.gamma block; .ok (fromPolicy v)) = _
    change ProverCommitPolicies25.gamma block = .ok v at hv
    rw [hv]
    rfl
  · simpa only [decode,roundtrip] using hd

#print axioms roundtrip
#print axioms gamma_installed
#print axioms ordinary_installed
#print axioms ordinary_rank
#print axioms gamma_rank
end R1Z.ProverRwDictionarySamplers
