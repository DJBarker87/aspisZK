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
 outer (Option.map unK) (OraclePortCkptAbi2Extracted.decode_k_spec b)
def parseE (b : Slice U8) : Result (Option Fresh.E) :=
 outer (Option.map unE) (OraclePortCkptAbi2Extracted.decode_e_spec b)
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

#print axioms raw
#print axioms raw_cut
#print axioms k_window
#print axioms e_window
end NJZ_Readers
