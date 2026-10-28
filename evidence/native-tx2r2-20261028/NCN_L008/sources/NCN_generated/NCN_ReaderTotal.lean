import NCN_WeightErrors
import NCI_SectionCursor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCN_ReaderTotal
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes4Sections

/-- Every sufficiently bounded section returns either the decoded section or
its first Checkpoint error; kernel failure is not silently excluded. -/
theorem section_total (n : Nat) (r : verifier.Reader)
    (bound : r.at.val+16*n ≤ r.bytes.val.length) :
    ∃ result, readList CheckpointBytes3Reader.readK n r = ok result := by
  induction n generalizing r with
  | zero => exact ⟨.Ok ([],r),rfl⟩
  | succ n ih =>
    have bound1 : r.at.val+16 ≤ r.bytes.val.length := by omega
    obtain ⟨b,out,_,advanced,backing,run⟩ := CheckpointBytes3Reader.read_k_c5 r bound1
    let value := CheckpointBytes3Reader.optionK
      ((ExactLeafFieldCodec.decodeQM31 (MultiproofConeCanonical.bytesOf b.val)).map
        CheckpointBytes3KDecode.rawK)
    have step : CheckpointBytes3Reader.readK r=ok (value,out) := run
    cases hv : value with
    | Err e =>
      refine ⟨.Err e,?_⟩
      simp only [readList,step,bind_tc_ok,hv]
    | Ok x =>
      have restBound : out.at.val+16*n ≤ out.bytes.val.length := by rw [backing]; omega
      obtain ⟨result,rest⟩ := ih out restBound
      cases result with
      | Err e =>
        refine ⟨.Err e,?_⟩
        simp only [readList,step,bind_tc_ok,hv,rest]
      | Ok pair =>
        rcases pair with ⟨xs,last⟩
        refine ⟨.Ok (x::xs,last),?_⟩
        simp only [readList,step,bind_tc_ok,hv,rest]

#print axioms section_total
end AspisR1.NCN_ReaderTotal
