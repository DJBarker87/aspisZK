import JFs_SerializerChain
set_option autoImplicit false
namespace AspisR1.JFs_SerializerFragment
open Aeneas Aeneas.Std Result
open AspisR1PublicSerializer.FieldsRefinement431
open AspisR1PublicSerializer.Frontier431
open AspisR1PublicSerializer.Whole431
open AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes

def run : Step → ByteVec → Result (Status × ByteVec)
  | .byte b,out => do let next ← alloc.vec.Vec.push out b;ok (.Ok (),next)
  | .words s,out => fields out s
  | .frontier f,out => frontier out f
  | .index n,out => do
      let next ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out (Array.to_slice (core.num.U64.to_le_bytes n))
      ok (.Ok (),next)

theorem source (s : Step) (out : ByteVec) (canon : canonical (stepWords s))
    (cap : out.length+(stepBytes s).length≤Usize.max) :
    ∃ updated,run s out=ok (.Ok (),updated) ∧ updated.val=out.val++stepBytes s := by
  cases s with
  | byte b =>
    have room : out.val.length<Usize.max := by
      simp only [stepBytes,List.length_cons,List.length_nil] at cap
      change out.val.length+1≤Usize.max at cap
      omega
    obtain ⟨updated,call,bytes⟩:=WP.spec_imp_exists (alloc.vec.Vec.push_spec out b room)
    exact ⟨updated,by simp only [run,call,bind_tc_ok],bytes⟩
  | words s =>
    have room : out.length+4*s.length≤Usize.max := by
      simpa only [stepBytes,JFs_SerializerLengths.words] using cap
    exact fields_canonical_append out s canon room
  | frontier f =>
    have room : out.length+4*((rows f).flatMap (fun s => s.val)).length≤Usize.max := by
      simpa only [stepBytes,JFs_SerializerLengths.words] using cap
    obtain ⟨updated,call,bytes⟩:=JFs_SerializerChain.source (rows f) out canon room
    refine ⟨updated,?_,bytes⟩
    exact (frontier_eq_chain out f).trans call
  | index n =>
    have room : out.length+(Array.to_slice (core.num.U64.to_le_bytes n)).length≤Usize.max := cap
    obtain ⟨updated,call,bytes⟩:=extend_u8 out (Array.to_slice (core.num.U64.to_le_bytes n)) room
    exact ⟨updated,by simp only [run,call,bind_tc_ok],bytes⟩

#print axioms source
end AspisR1.JFs_SerializerFragment
