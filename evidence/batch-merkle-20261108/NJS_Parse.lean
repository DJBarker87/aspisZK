import NJS_Extract.Funs
import Op3I_ParseLaws
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NJS_Parse
open Aeneas Aeneas.Std Result

def variant : NJS_Extract.transport.Variant → Op3I_Source.transport.Variant
 | .S1 => .S1 | .S2 => .S2 | .D => .D

def error : NJS_Extract.verifier.Error → Op3I_Source.verifier.Error
 | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript | .Relation => .Relation
 | .Merkle => .Merkle | .Query => .Query | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def reply : core.result.Result NJS_Extract.transport.Variant NJS_Extract.verifier.Error →
 core.result.Result Op3I_Source.transport.Variant Op3I_Source.verifier.Error
 | .Ok v => .Ok (variant v) | .Err e => .Err (error e)

def map {A B : Type} (f : A→B) (r : Result A) : Result B := do let a←r;ok (f a)

theorem map_bind {A B C : Type} (f : A→B) (r : Result C) (k : C→Result A) :
 map f (do let c←r;k c)=(do let c←r;map f (k c)) := by cases r <;> rfl

theorem map_ite {A B : Type} (f : A→B) (p : Prop) [Decidable p] (x y : Result A) :
 map f (if p then x else y) = if p then map f x else map f y := by split <;>rfl

theorem map_ok {A B : Type} (f : A→B) (x : A) : map f (ok x)=ok (f x) := rfl

-- Constant-body equality is generated below; no numeral evaluation of a recurrence.
theorem proof_bytes : NJS_Extract.compact.PROOF_BYTES=Op3I_Source.compact.PROOF_BYTES := by
  simp only [NJS_Extract.compact.COMPACT_SEMANTIC,
    NJS_Extract.compact.COMPACT_Y1,
    NJS_Extract.compact.FINAL_LEN,
    NJS_Extract.compact.FIXED,
    NJS_Extract.compact.HEADER,
    NJS_Extract.compact.LOGICAL_SEMANTIC,
    NJS_Extract.compact.MAGIC,
    NJS_Extract.compact.MAX_NODES,
    NJS_Extract.compact.MAX_PROOF,
    NJS_Extract.compact.OFF_FINAL,
    NJS_Extract.compact.OFF_FOLDED_ROOT,
    NJS_Extract.compact.OFF_INACTIVE,
    NJS_Extract.compact.OFF_NODES,
    NJS_Extract.compact.OFF_OPENINGS,
    NJS_Extract.compact.OFF_ROUND0,
    NJS_Extract.compact.OFF_ROUND1,
    NJS_Extract.compact.OFF_SEMANTIC,
    NJS_Extract.compact.OFF_Y1,
    NJS_Extract.compact.OPENING,
    NJS_Extract.compact.PROOF_BYTES,
    NJS_Extract.compact.QUERIES,
    NJS_Extract.compact.SEMANTIC_COMPACT_VALUES,
    NJS_Extract.verifier.SEMANTIC_BYTES,
    Op3I_Source.compact.COMPACT_SEMANTIC,
    Op3I_Source.compact.COMPACT_Y1,
    Op3I_Source.compact.FINAL_LEN,
    Op3I_Source.compact.FIXED,
    Op3I_Source.compact.HEADER,
    Op3I_Source.compact.LOGICAL_SEMANTIC,
    Op3I_Source.compact.MAGIC,
    Op3I_Source.compact.MAX_NODES,
    Op3I_Source.compact.MAX_PROOF,
    Op3I_Source.compact.OFF_FINAL,
    Op3I_Source.compact.OFF_FOLDED_ROOT,
    Op3I_Source.compact.OFF_INACTIVE,
    Op3I_Source.compact.OFF_NODES,
    Op3I_Source.compact.OFF_OPENINGS,
    Op3I_Source.compact.OFF_ROUND0,
    Op3I_Source.compact.OFF_ROUND1,
    Op3I_Source.compact.OFF_SEMANTIC,
    Op3I_Source.compact.OFF_Y1,
    Op3I_Source.compact.OPENING,
    Op3I_Source.compact.PROOF_BYTES,
    Op3I_Source.compact.QUERIES,
    Op3I_Source.compact.SEMANTIC_COMPACT_VALUES,
    Op3I_Source.verifier.SEMANTIC_BYTES]

theorem predicate :
 NJS_Extract.verifier.candidate.parse_shape.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool =
 Op3I_Source.verifier.candidate.parse_shape.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool := rfl

theorem map_pair {A B C D : Type} (f : C→D) (p : A×B) (k : A→B→Result C) :
 map f (let (a,b):=p;k a b) = (let (a,b):=p;map f (k a b)) := by cases p;rfl

theorem final {S : Type} (p : Bool×S) :
 map reply (let (b,_):=p;if b then ok (.Err NJS_Extract.verifier.Error.Parse) else ok (.Ok NJS_Extract.transport.Variant.S2)) =
 (let (b,_):=p;if b then ok (.Err Op3I_Source.verifier.Error.Parse) else ok (.Ok Op3I_Source.transport.Variant.S2)) := by
 rcases p with ⟨b,s⟩;cases b <;>rfl

theorem bind_same {A B : Type} (m : Result A) (f g : A→Result B) (h : ∀ a,f a=g a) :
 (do let a←m;f a)=(do let a←m;g a) := by cases m <;> simp_all

theorem source (proof : Slice U8) :
 map reply (NJS_Extract.verifier.candidate.parse_shape Op3I_Std.ops.sliceNe Op3I_Std.ops.sliceEq Op3I_Std.ops.iterAny proof) =
 Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops proof := by
 simp only [NJS_Extract.verifier.candidate.parse_shape, Op3I_Source.verifier.candidate.parse_shape,
   proof_bytes,Op3I_Header.proof_bytes,map_bind,map_ite,map_ok,map_pair,final,reply,variant,error,predicate,
   NJS_Extract.compact.MAGIC,Op3I_Source.compact.MAGIC,bind_tc_ok,
   NJS_Extract.Slice.Insts.CoreCmpPartialEqArray,Op3I_Source.Slice.Insts.CoreCmpPartialEqArray,
   NJS_Extract.transport.Variant.tag,Op3I_Source.transport.Variant.tag]
 by_cases length : (Slice.len proof != 57607#usize)=true
 · simp only [if_pos length]
 · simp only [if_neg length]
   apply bind_same
   intro headBytes
   apply bind_same
   intro wrongMagic
   by_cases magic : wrongMagic=true
   · simp only [if_pos magic]
   · simp only [if_neg magic]
     apply bind_same
     intro tag
     by_cases badTag : (tag != 2#u8)=true
     · simp only [if_pos badTag]
     · simp only [if_neg badTag]
       apply bind_same
       intro tail
       apply bind_same
       intro iter
       apply bind_same
       rintro ⟨hit,rest⟩
       cases hit <;>rfl

#check source
#print axioms bind_same
#print axioms map_bind
#print axioms map_ite
#print axioms final
#print axioms map_pair
#print axioms predicate
#print axioms map_ok
#print axioms proof_bytes
#print axioms source
end NJS_Parse
