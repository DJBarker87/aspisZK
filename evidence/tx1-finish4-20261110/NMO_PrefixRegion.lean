import NMO_PrefixStep
import ExtractedPrefixParse
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_PrefixRegion
open Aeneas Aeneas.Std Result AspisR1PrefixAggregateParser ExtractedPrefixTrace
/-- Symbolic chain induction precedes the fixed 27-row extent calculation. -/
theorem total {bytes : Slice U8} {rows : List U8} {offset finish : Usize}
 {frames : List (Slice U8)} (chain : RecordChain bytes rows offset frames finish) :
 finish.val=offset.val+(rows.map (fun row => NGX_PrefixGeometry.width row.val)).sum := by
 induction chain with
 | nil offset => simp
 | @cons row rows offset frame next frames finish step tail ih =>
  have advance := (NMO_PrefixStep.geometry bytes frame row offset next step).1
  rw [ih,advance]
  simp only [List.map_cons,List.sum_cons]
  omega
/-- Every stored record is a window of the SAME original parser buffer. -/
theorem windows {bytes : Slice U8} {rows : List U8} {offset finish : Usize}
 {frames : List (Slice U8)} (chain : RecordChain bytes rows offset frames finish) :
 ∀ frame∈frames,∃ start : Nat,start+frame.val.length≤bytes.val.length ∧
 frame.val=List.slice start (start+frame.val.length) bytes.val := by
 induction chain with
 | nil offset => simp
 | @cons row rows offset frame next frames finish step tail ih =>
  intro record member
  rcases List.mem_cons.mp member with same | member
  · subst record
    have geom := NMO_PrefixStep.geometry bytes frame row offset next step
    have length := NIX_PredecessorFrames.record_at bytes frame row offset next step
    have endAt : next.val=offset.val+frame.val.length := by rw [length];exact geom.1
    refine ⟨offset.val,?_,?_⟩
    · rw [←endAt];exact geom.2.2.1
    · rw [←endAt];exact geom.2.2.2
  · exact ih record member
/-- Original caller provenance supplies the exact extent and every current
record window, without adding any endpoint or child-success premise. -/
theorem source {H : Type} (input : NLU.Input H) (domain : NLU.InputDomain input) :
 ∃ bytes : Slice U8,bytes.val.length=13831 ∧
 ∀ frame∈input.prefix1.records.val,∃ start : Nat,
 start+frame.val.length≤bytes.val.length ∧
 frame.val=List.slice start (start+frame.val.length) bytes.val := by
 obtain ⟨bytes,pre,parsed,same⟩ := domain.parsedPrefix
 obtain ⟨_,finish,chain,endAt⟩ := ExtractedPrefixParse.parse_success bytes pre parsed
 have sum : (rowOrder.map (fun row => NGX_PrefixGeometry.width row.val)).sum=13799 := by decide
 have extent := total chain
 rw [endAt,sum] at extent
 change bytes.val.length=13831 at extent
 refine ⟨bytes,extent,?_⟩
 intro frame member
 rw [same] at member
 change frame∈pre.records.val at member
 exact windows chain frame member
#print axioms total
#print axioms windows
#print axioms source
set_option pp.proofs false in #print source
end AspisR1.NMO_PrefixRegion
end
