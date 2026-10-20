import AspisR1Stage2AdoptedResume.Funs
import Stage2ResumeFixedReadPrefix
import Stage2GeneratedPrefixReaderBridge

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Stage2AdoptedReader.GeneratedPrefixBridgeProof

abbrev GenReader := AspisR1Stage2AdoptedResume.verifier.Reader
abbrev ReadReader := AspisR1Stage2AdoptedReader.verifier.Reader

def toGenReader (r : ReadReader) : GenReader := { bytes := r.bytes, «at» := r.«at» }

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

theorem mapResult_bind {A B C : Type} (f : B → C) (m : Result A) (k : A → Result B) :
    (mapResult f (do
      let a ← m
      k a)) = (do
      let a ← m
      mapResult f (k a)) := by
  cases m <;> rfl

attribute [local irreducible] mapResult

def mapRawResult {n : Usize} (r : Result ((Array Std.U8 n) × ReadReader)) :
    Result ((Array Std.U8 n) × GenReader) :=
  mapResult (fun p => (p.1, toGenReader p.2)) r

theorem raw_equiv (n : Usize) (r : ReadReader) :
    mapRawResult (AspisR1Stage2AdoptedReader.verifier.Reader.raw
      AspisR1Stage2AdoptedReader.GeneratedPrefixBridge.readerDecodersForGenerated n r) =
      AspisR1Stage2AdoptedResume.verifier.Reader.raw n (toGenReader r) := by
  unfold mapRawResult
  unfold AspisR1Stage2AdoptedReader.verifier.Reader.raw
    AspisR1Stage2AdoptedResume.verifier.Reader.raw
    AspisR1Stage2AdoptedReader.GeneratedPrefixBridge.readerDecodersForGenerated
  simp only [mapResult_bind]
  simp only [mapResult, toGenReader]

#print axioms raw_equiv

end AspisR1Stage2AdoptedReader.GeneratedPrefixBridgeProof
