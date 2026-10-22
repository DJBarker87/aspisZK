import CheckpointBytes4ReaderFields
import CheckpointBytes4Ops

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytes4RawFields
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes3Reader OraclePortCkptAbiSourceFields

theorem raw_success (n : Usize) (r out : verifier.Reader) (b : Array U8 n)
    (bound : r.at.val+n.val ≤ r.bytes.val.length)
    (success : raw n r = ok (b,out)) :
    b.val = (r.bytes.val.drop r.at.val).take n.val ∧
      out.at.val = r.at.val+n.val ∧ out.bytes = r.bytes := by
  obtain ⟨actual,last,run,contents,cursor,backing⟩ :=
    OraclePortCkptAbi2Unwrap.raw_panic_unreachable r n (fun _ => fail .panic) bound
  have eq : (actual,last) = (b,out) := Result.ok.inj (run.symm.trans success)
  have hb := congrArg Prod.fst eq
  have hr := congrArg Prod.snd eq
  dsimp only at hb hr
  subst actual out
  exact ⟨contents,cursor,backing⟩

/-- Query parsing advances four bytes per executed query, retaining the same
backing. It does not yet identify from_le_bytes with the flat query decoder. -/
theorem query_cursor (reserved : Bool) (r out : verifier.Reader) (qs : List U32)
    (reads : QueryReads (CheckpointBytes4Ops.ops reserved) r qs out)
    (bound : r.at.val+qs.length*4 ≤ r.bytes.val.length) :
    out.at.val = r.at.val+qs.length*4 ∧ out.bytes = r.bytes := by
  induction reads with
  | nil r => exact ⟨by simp,rfl⟩
  | @cons r next last b q qs first decode tail ih =>
    obtain ⟨_,cursor,backing⟩ := raw_success 4#usize r next b (by
      simp only [List.length_cons] at bound
      change r.at.val+4 ≤ r.bytes.val.length
      omega) first
    change next.at.val = r.at.val+4 at cursor
    obtain ⟨lastCursor,lastBacking⟩ := ih (by rw [backing,cursor]; simp only [List.length_cons] at bound; omega)
    exact ⟨by simp only [List.length_cons]; omega,lastBacking.trans backing⟩

#print axioms raw_success
#print axioms query_cursor
end AspisR1.CheckpointBytes4RawFields
end
