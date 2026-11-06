import NJC_ReaderEmission
import NJC_ReaderWindows
import NIL_ResultTransport
set_option autoImplicit false
noncomputable section
namespace NJC_RawPort
open Aeneas Aeneas.Std Result AspisR1 NIL_Carriers NIL_ResultTransport

/-- Literal emitted raw body, with its debug-bearing unwrap boundary explicit.
No concrete Formatter axiom is imported or assumed. -/
theorem transport (n : Usize)
 (unwrap : core.result.Result (Array U8 n) core.array.TryFromSliceError → Result (Array U8 n))
 (r : Fresh.R) :
 outer (fun p=>(p.1,reader p.2)) (NJC_ReaderEmission.verifier.Reader.raw n unwrap r)=
 AspisR1Stage2.verifier.Reader.rawWithUnwrap n unwrap (reader r) := by
 simp only [NJC_ReaderEmission.verifier.Reader.raw,AspisR1Stage2.verifier.Reader.rawWithUnwrap,
  reader,outer_bind]
 rfl

/-- Full byte and backing frame of that exact body at every bounded cursor.
The unwrap law is a named unresolved concrete boundary, not a successful raw
reply or endpoint equation. -/
theorem bounded (n : Usize)
 (unwrap : core.result.Result (Array U8 n) core.array.TryFromSliceError → Result (Array U8 n))
 (unwrap_ok : ∀ b,unwrap (.Ok b)=ok b)
 (r : Fresh.R) (bound : r.at.val+n.val≤r.bytes.val.length) :
 ∃ b : Array U8 n, ∃ out : Fresh.R,
 NJC_ReaderEmission.verifier.Reader.raw n unwrap r=ok (b,out) ∧
 b.val=(r.bytes.val.drop r.at.val).take n.val ∧
 out.at.val=r.at.val+n.val ∧ out.bytes=r.bytes := by
 obtain ⟨b,out,run,contents,cursor,backing⟩ :=
  OraclePortCkptAbiReader.raw_total_exact (reader r) n unwrap unwrap_ok bound
 rw [← transport] at run
 obtain ⟨p,freshRun,same⟩ := (outer_ok_iff _ _ _).mp run
 have cb : p.1=b := congrArg Prod.fst same
 have cr : reader p.2=out := congrArg Prod.snd same
 refine ⟨p.1,p.2,freshRun,?_,?_,?_⟩
 · rw [cb];exact contents
 · change (reader p.2).at.val=_
   rw [cr];exact cursor
 · change (reader p.2).bytes=_
   rw [cr];exact backing

#print axioms transport
#print axioms bounded
end NJC_RawPort
