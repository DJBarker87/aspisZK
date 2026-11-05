import NHG_FrontierFrame
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NHG_FrontierPackets
open SerializerFields NHG_FrontierFrame
abbrev Packet := ByteVec → Slice U32 → Result (Status × ByteVec)

def chainWith (packet : Packet) : List (Slice U32) → ByteVec → Result (Status × ByteVec)
 | [],out => ok (.Ok (),out)
 | s::ss,out => thenCheck (packet out s) (chainWith packet ss)

/-- Each actual caller supplies the child domain. The packet law is required
on that domain only, and includes status and the complete mutated Vec. -/
theorem transport (packet : Packet)
 (law : ∀ out s,1≤out.val.length → s.length≤8 → out.val.length+4*s.length≤1880 →
  packet out s=NHG_FieldSpec.fields out s)
 (ss : List (Slice U32)) (out : ByteVec) (nonempty : 1≤out.val.length)
 (widths : ∀ s∈ss,s.length≤8) (cap : out.val.length+4*words ss≤1880) :
 chainWith packet ss out=chain ss out := by
 induction ss generalizing out with
 | nil => rfl
 | cons s ss ih =>
   have count : words (s::ss)=s.length+words ss := by simp [words]
   have width:=widths s (by simp)
   have platform : 1880≤Usize.max := by scalar_tac
   have localCap : out.val.length+4*s.length≤1880 := by rw [count] at cap;omega
   rw [chainWith,law out s nonempty width localCap,chain]
   obtain ⟨⟨status,mid⟩,call,lo,hi,tail,frame⟩:=NHG_FieldBounds.source out s (by change out.val.length+4*s.length≤Usize.max;omega)
   change out.val.length≤mid.val.length at lo
   change mid.val.length≤out.val.length+4*s.length at hi
   rw [call]
   cases status with
   | Err e => rfl
   | Ok u =>
     change chainWith packet ss mid=chain ss mid
     apply ih mid (by omega)
     · intro t ht;exact widths t (by simp only [List.mem_cons];exact Or.inr ht)
     · rw [count] at cap;omega

theorem row_widths (values : Array (Array U32 8#usize) 20#usize) :
 ∀ s∈AspisR1PublicSerializer.Frontier431.rows values,s.length≤8 := by
 intro s member
 simp only [AspisR1PublicSerializer.Frontier431.rows,List.mem_cons,List.not_mem_nil,
  or_false] at member
 rcases member with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
  subst s <;> exact Nat.le_of_eq (row_length _ _)

theorem source (packet : Packet)
 (law : ∀ out s,1≤out.val.length → s.length≤8 → out.val.length+4*s.length≤1880 →
  packet out s=NHG_FieldSpec.fields out s)
 (out : ByteVec) (values : Array (Array U32 8#usize) 20#usize)
 (nonempty : 1≤out.val.length) (cap : out.val.length≤1240) :
 pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier out values=
 chainWith packet (AspisR1PublicSerializer.Frontier431.rows values) out := by
 rw [NHG_FrontierFrame.source]
 symm
 apply transport packet law _ out nonempty (row_widths values)
 rw [row_count]
 omega

theorem closed_packets (out : ByteVec)
 (values : Array (Array U32 8#usize) 20#usize)
 (nonempty : 1≤out.val.length) (cap : out.val.length≤1240) :
 pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier out values=
 chainWith NHG_FieldSpec.fields (AspisR1PublicSerializer.Frontier431.rows values) out :=
 source NHG_FieldSpec.fields (fun _ _ _ _ _=>rfl) out values nonempty cap

#print axioms closed_packets
#print axioms transport
#print axioms row_widths
#print axioms source
end AspisR1.NHG_FrontierPackets
