import Port4B_Opening
import CheckpointBytes5Inputs

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_LeafCode
open Aeneas Aeneas.Std Result
open CheckpointBytes5Effect
open MultiproofConeCanonical MultiproofConeSlices
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

/-- P6 leaf lowering: source salt-copy/range operations are pure. These
three physical components are passed to the actual digest operation once. -/
def parts (tag : U8) (value salt : Slice U8) : Parts :=
  ⟨[⟨[16#u8,tag],by simp;scalar_tac⟩,value,salt],by simp;scalar_tac⟩

def readRange (o : Slice U8) (start finish : Usize) : Result (Slice U8) :=
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    o {start:=start,«end»:=finish}

def codeFor (o : Slice U8) (tag : U8) (vs ve ss se : Usize) : Code Digest :=
  .step (readRange o ss se) fun salt =>
  .step (readRange o vs ve) fun value =>
  .read (parts tag value salt) .done

def code (kind : Usize) (o : Slice U8) : Code Digest :=
  if kind=0#usize then codeFor o 113#u8 0#usize 480#usize 608#usize 640#usize
  else if kind=1#usize then codeFor o 241#u8 480#usize 608#usize 640#usize 672#usize
  else codeFor o 114#u8 672#usize 800#usize 800#usize 832#usize

def native {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X)
    (hash : X) (kind : Usize) (o : Slice U8) : Result Digest := erase D hash (code kind o)

/-- The SINGLE source digest address as physical component slices. -/
def input (kind : Usize) (o : Slice U8) : Parts :=
  if kind=0#usize then parts 113#u8 (sub o 0#usize 480#usize) (sub o 608#usize 640#usize)
  else if kind=1#usize then parts 241#u8 (sub o 480#usize 608#usize) (sub o 640#usize 672#usize)
  else parts 114#u8 (sub o 672#usize 800#usize) (sub o 800#usize 832#usize)

theorem code_exact {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X)
    (hash : X) (kind : Usize) (o : Slice U8) (len : o.val.length=832) (before : Log) :
    erase D hash (code kind o)=D.digest hash (input kind o) ∧
    run D hash (code kind o) before =
      (do let d ← D.digest hash (input kind o); ok (d,before++[(input kind o,d)])) := by
  have range (s e : Usize) (order : s.val≤e.val) (fit : e.val≤832) :
      readRange o s e=ok (sub o s e) :=
    range_total o s e order (by omega)
  unfold code input
  split
  · simp only [codeFor,erase,run,bind_tc_ok,range 608#usize 640#usize (by decide) (by decide),
      range 0#usize 480#usize (by decide) (by decide),erase,run,bind_tc_ok]
    constructor <;> rfl
  · split
    · simp only [codeFor,erase,run,bind_tc_ok,range 640#usize 672#usize (by decide) (by decide),
        range 480#usize 608#usize (by decide) (by decide),erase,run,bind_tc_ok]
      constructor <;> rfl
    · simp only [codeFor,erase,run,bind_tc_ok,range 800#usize 832#usize (by decide) (by decide),
        range 672#usize 800#usize (by decide) (by decide),erase,run,bind_tc_ok]
      constructor <;> rfl

theorem address (kind : Usize) (o : Slice U8) :
    flatten (input kind o) = MultiproofConeOpeningAdapters.leafAddress kind.val (bytesOf o.val) := by
  have zero : kind=0#usize ↔ kind.val=0 := by
    constructor
    · intro h;subst kind;rfl
    · intro h;exact UScalar.eq_of_val_eq h
  have one : kind=1#usize ↔ kind.val=1 := by
    constructor
    · intro h;subst kind;rfl
    · intro h;exact UScalar.eq_of_val_eq h
  unfold input MultiproofConeOpeningAdapters.leafAddress
  simp only [zero,one]
  split <;> (try split) <;>
    simp [parts,flatten,sub,bytesOf,OraclePortCompactDraft.slice,List.map_take,List.map_drop,decodeByte]

/-- Exact one-read native interpretation and ordered effect on ANY initial
log. The hash return is the same value subsequently used by dedup/write. -/
theorem native_and_reads {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X)
    (hash : X) (H : Bytes → State)
    (law : ∀ p, D.digest hash p=ok (MultiproofConePhysicalTransport.rawOracle H p))
    (kind : Usize) (o : Slice U8) (len : o.val.length=832) (before : Log) :
    native D hash kind o=ok (encodeState (H (flatten (input kind o)))) ∧
    run D hash (code kind o) before =
      ok (encodeState (H (flatten (input kind o))),
        before++[(input kind o,encodeState (H (flatten (input kind o))))]) := by
  have exactCode := code_exact D hash kind o len before
  simp only [law,MultiproofConePhysicalTransport.rawOracle,bind_tc_ok] at exactCode
  exact exactCode

#print axioms code_exact
#print axioms address
#print axioms native_and_reads
end AspisR1.Port4B_LeafCode
end
