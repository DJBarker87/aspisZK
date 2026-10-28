import R1Z.PV_RunJoin_ClaimBytes41
import R1Z.PV_RunJoin_HighAppend41
import R1Z.PV_RunJoin_ArrayEntries41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimCanonical41
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_PolyCell38 PV_RunJoin_PolyLoop38 PV_RunJoin_ClaimBytes41
variable [ExternalTypes]

theorem high (p : Nat → Nat → Q) (extras : Nat → Q) :
    PV_RunJoin_HighDomain40.HighZero (bytes p extras) := by
  have h0 := PV_RunJoin_PolyCanonical40.high (p 0) 0 29
  have h1 := PV_RunJoin_PolyCanonical40.high (p 1) 0 29
  have h2 := PV_RunJoin_PolyCanonical40.high (p 2) 0 29
  have he := PV_RunJoin_PolyCanonical40.high extras 0 29
  have h01 := PV_RunJoin_HighAppend41.append _ _ 29 (payload_length _ _ _) h0 h1
  have h012 := PV_RunJoin_HighAppend41.append _ _ 58
    (by rw [List.length_append,payload_length,payload_length]) h01 h2
  exact PV_RunJoin_HighAppend41.append _ _ 87
    (by rw [List.length_append,List.length_append,payload_length,payload_length,payload_length]) h012 he

/-- The actual caller's claim_bytes accepts all its actual array carriers and
always emits 3712 canonical bytes. No source-loop success is assumed. -/
theorem encode (ops : ExternalFuns) (claims : Array (Array Q 29#usize) 3#usize)
    (extras : Array Q 29#usize) :
    ∃ next, @host_semantic.claim_bytes _ (ProverRwP6BodyCandidate.selected ops)
      claims extras=.ok next ∧ next.length=3712 ∧
      PV_RunJoin_HighDomain40.HighZero next.val := by
  let zero : Q := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
  let row := PV_RunJoin_ArrayEntries41.entries claims extras
  let p := fun i => PV_RunJoin_ArrayEntries41.entries (row i) zero
  let e := PV_RunJoin_ArrayEntries41.entries extras zero
  have rows : ProverCommitArray49.array 3#usize
      (fun i => ProverCommitArray49.array 29#usize (p i))=claims := by
    have h : (fun i => ProverCommitArray49.array 29#usize (p i))=row := by
      funext i
      exact PV_RunJoin_ArrayEntries41.rebuild (row i) zero
    rw [h]
    exact PV_RunJoin_ArrayEntries41.rebuild claims extras
  obtain ⟨next,hn,hv,hl⟩ := PV_RunJoin_ClaimBytes41.encode ops p e
  rw [rows,PV_RunJoin_ArrayEntries41.rebuild extras zero] at hn
  exact ⟨next,hn,hl,by rw [hv];exact high p e⟩
#print axioms high
#print axioms encode
end R1Z.PV_RunJoin_ClaimCanonical41
