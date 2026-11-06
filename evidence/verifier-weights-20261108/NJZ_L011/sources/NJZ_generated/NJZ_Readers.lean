import NJC_ConcreteUnwrap
import NJC_RawWindows
import NJC_EReaderResults
set_option autoImplicit false
noncomputable section
namespace NJZ_Readers
open Aeneas Aeneas.Std Result AspisR1 NIL_Carriers

/-- Concrete parser carrier transport; TX2:019 and TX2:031 give the codecs.
The parser input is the SAME emitted raw window, not an independent reply. -/
def parseK (b : Slice U8) : Result (Option Fresh.K) :=
 outer (Option.map (unK ∘ CheckpointBytes3Namespaces.fromK)) (OraclePortCkptAbi2Extracted.decode_k_spec b)
def parseE (b : Slice U8) : Result (Option Fresh.E) :=
 outer (Option.map (unE ∘ CheckpointBytes3Namespaces.fromE)) (OraclePortCkptAbi2Extracted.decode_e_spec b)
def k (r : Fresh.R) := NJC_ReaderEmission.verifier.Reader.k
 (core.result.Result.unwrap core.fmt.DebugTryFromSliceError) parseK r
def e (r : Fresh.R) := NJC_ReaderEmission.verifier.Reader.e
 (core.result.Result.unwrap core.fmt.DebugTryFromSliceError) parseE r

/-- Full raw Result with concrete Std unwrap and no operation dictionary. -/
theorem raw (n : Usize) (r : Fresh.R) :
 NJC_ConcreteUnwrap.raw n r=NIL_FreshOps.raw n r :=
 NJC_ConcreteUnwrap.clause n r

/-- The raw cut contains only arbitrary-index bytes, cursor and backing frame,
as asserted by NJJ raw4/16/32 windows. No pointer-to-payload inference. -/
def RawCut (n : Usize) (r out : Fresh.R) (bytes : Array U8 n) : Prop :=
 bytes.val=(r.bytes.val.drop r.at.val).take n.val ∧
 out.at.val=r.at.val+n.val ∧ out.bytes=r.bytes

theorem raw_cut (n : Usize) (r : Fresh.R)
 (bound : r.at.val+n.val≤r.bytes.val.length) :
 ∃ bytes out, RawCut n r out bytes ∧ NJC_ConcreteUnwrap.raw n r=ok (bytes,out) := by
 obtain ⟨bytes,out,run,contents,cursor,backing⟩:=NJC_ConcreteUnwrap.bounded n r bound
 exact ⟨bytes,out,⟨contents,cursor,backing⟩,run⟩

/-- Same-window lifting retains all parser Result arms on the frozen body. -/
theorem k_window (r : Fresh.R) (bound : r.at.val+16≤r.bytes.val.length) :
 ∃ bytes : Array U8 16#usize, ∃ out : Fresh.R,
 RawCut 16#usize r out bytes ∧
 k r=(do let (reply,_) ← k {bytes:=bytes.to_slice,«at»:=0#usize};ok (reply,out)) := by
 obtain ⟨bytes,out,contents,cursor,backing,run⟩ := NJC_RawWindows.k
  _ (NJC_ConcreteUnwrap.source _) parseK r bound
 exact ⟨bytes,out,⟨contents,cursor,backing⟩,run⟩

theorem e_window (r : Fresh.R) (bound : r.at.val+32≤r.bytes.val.length) :
 ∃ bytes : Array U8 32#usize, ∃ out : Fresh.R,
 RawCut 32#usize r out bytes ∧
 e r=(do let (reply,_) ← e {bytes:=bytes.to_slice,«at»:=0#usize};ok (reply,out)) := by
 obtain ⟨bytes,out,contents,cursor,backing,run⟩ := NJC_RawWindows.e
  _ (NJC_ConcreteUnwrap.source _) parseE r bound
 exact ⟨bytes,out,⟨contents,cursor,backing⟩,run⟩

/-- Frozen K reader after CLOSED codec substitution on the SAME raw window.
Both canonical and Checkpoint error replies retain the advanced Reader. -/
theorem k_source (r : Fresh.R) (bound : r.at.val+16≤r.bytes.val.length) :
 ∃ bytes : Array U8 16#usize, ∃ out : Fresh.R,
 RawCut 16#usize r out bytes ∧
 k r=ok (unInner unK (NJC_ReaderResults.naturalK bytes),out) := by
 obtain ⟨bytes,out,cut,run⟩ := raw_cut 16#usize r bound
 refine ⟨bytes,out,cut,?_⟩
 unfold k NJC_ReaderEmission.verifier.Reader.k
 unfold NJC_ConcreteUnwrap.raw at run
 rw [run]
 simp only [bind_tc_ok]
 change (do let value ← parseK bytes.to_slice
            let reply ← NJC_ReaderEmission.core.option.Option.ok_or value
              NID_ResumeEmission.verifier.Error.Checkpoint
            ok (reply,out))=_
 have codec := NJC_ReaderResults.decodeK bytes
 cases h : OraclePortCkptAbi2Extracted.decode_k_spec bytes.to_slice with
 | fail err => simp only [h,bind_tc_fail] at codec; cases codec
 | div => simp only [h,bind_tc_div] at codec; cases codec
 | ok value =>
   simp only [h,bind_tc_ok] at codec
   have valueEq := Result.ok.inj codec
   cases value <;> simp only [CheckpointBytes3Reader.optionK] at valueEq <;>
    simp [parseK,h,outer,NJC_ReaderEmission.core.option.Option.ok_or,
      unInner,unError,←valueEq,Function.comp_def]

/-- Frozen E reader after CLOSED codec substitution on the SAME raw window.
Both canonical and Checkpoint error replies retain the advanced Reader. -/
theorem e_source (r : Fresh.R) (bound : r.at.val+32≤r.bytes.val.length) :
 ∃ bytes : Array U8 32#usize, ∃ out : Fresh.R,
 RawCut 32#usize r out bytes ∧
 e r=ok (unInner unE (NJC_EReaderResults.naturalE bytes),out) := by
 obtain ⟨bytes,out,cut,run⟩ := raw_cut 32#usize r bound
 refine ⟨bytes,out,cut,?_⟩
 unfold e NJC_ReaderEmission.verifier.Reader.e
 unfold NJC_ConcreteUnwrap.raw at run
 rw [run]
 simp only [bind_tc_ok]
 change (do let value ← parseE bytes.to_slice
            let reply ← NJC_ReaderEmission.core.option.Option.ok_or value
              NID_ResumeEmission.verifier.Error.Checkpoint
            ok (reply,out))=_
 have codec := NJC_EReaderResults.decodeE bytes
 cases h : OraclePortCkptAbi2Extracted.decode_e_spec bytes.to_slice with
 | fail err => simp only [h,bind_tc_fail] at codec; cases codec
 | div => simp only [h,bind_tc_div] at codec; cases codec
 | ok value =>
   simp only [h,bind_tc_ok] at codec
   have valueEq := Result.ok.inj codec
   cases value <;> simp only [CheckpointBytes3Reader.optionE] at valueEq <;>
    simp [parseE,h,outer,NJC_ReaderEmission.core.option.Option.ok_or,
      unInner,unError,←valueEq,Function.comp_def]

/-- All pre-states, including raw panic/divergence: concrete child/parser
substitution equals the adopted Reader model with exact nominal transport. -/
theorem k_reference (r : Fresh.R) : k r=NIL_FreshOps.readK r := by
 unfold k NJC_ReaderEmission.verifier.Reader.k
 change (do let (bytes,out) ← NJC_ConcreteUnwrap.raw 16#usize r
            let value ← parseK bytes.to_slice
            let reply ← NJC_ReaderEmission.core.option.Option.ok_or value
              NID_ResumeEmission.verifier.Error.Checkpoint
            ok (reply,out))=_
 rw [raw]
 unfold NIL_FreshOps.raw NIL_FreshOps.readK CheckpointBytes3Reader.readK
 cases hraw : CheckpointBytes3Reader.raw 16#usize (reader r) with
 | fail err => rfl
 | div => rfl
 | ok pair =>
   rcases pair with ⟨bytes,out⟩
   simp only [outer,bind_tc_ok]
   unfold parseK
   dsimp only
   cases hparse : OraclePortCkptAbi2Extracted.decode_k_spec bytes.to_slice with
   | fail err => rfl
   | div => rfl
   | ok value => cases value <;> rfl

/-- All pre-states, including raw panic/divergence: concrete child/parser
substitution equals the adopted Reader model with exact nominal transport. -/
theorem e_reference (r : Fresh.R) : e r=NIL_FreshOps.readE r := by
 unfold e NJC_ReaderEmission.verifier.Reader.e
 change (do let (bytes,out) ← NJC_ConcreteUnwrap.raw 32#usize r
            let value ← parseE bytes.to_slice
            let reply ← NJC_ReaderEmission.core.option.Option.ok_or value
              NID_ResumeEmission.verifier.Error.Checkpoint
            ok (reply,out))=_
 rw [raw]
 unfold NIL_FreshOps.raw NIL_FreshOps.readE CheckpointBytes3Reader.readE
 cases hraw : CheckpointBytes3Reader.raw 32#usize (reader r) with
 | fail err => rfl
 | div => rfl
 | ok pair =>
   rcases pair with ⟨bytes,out⟩
   simp only [outer,bind_tc_ok]
   unfold parseE
   dsimp only
   cases hparse : OraclePortCkptAbi2Extracted.decode_e_spec bytes.to_slice with
   | fail err => rfl
   | div => rfl
   | ok value => cases value <;> rfl

#print axioms raw
#print axioms raw_cut
#print axioms k_window
#print axioms e_window
#print axioms k_source
#print axioms e_source
#print axioms k_reference
#print axioms e_reference
end NJZ_Readers
