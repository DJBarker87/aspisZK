import NHG_FieldBounds
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NHG_FrontierFrame
open SerializerFields
abbrev Status := core.result.Result Unit NewError

def thenCheck (m : Result (Status × ByteVec))
 (k : ByteVec → Result (Status × ByteVec)) : Result (Status × ByteVec) := do
 let (s,out) ← m
 match s with
 | .Ok _ => k out
 | .Err e => ok (.Err e,out)

def chain : List (Slice U32) → ByteVec → Result (Status × ByteVec)
 | [],out => ok (.Ok (),out)
 | s::ss,out => thenCheck (NHG_FieldSpec.fields out s) (chain ss)

def words (ss : List (Slice U32)) : Nat := (ss.map (fun s=>s.length)).sum

theorem envelope (ss : List (Slice U32)) (out : ByteVec)
 (cap : out.val.length+4*words ss≤Usize.max) :
 ∃ r, chain ss out=ok r ∧ out.val.length≤r.2.val.length ∧
 r.2.val.length≤out.val.length+4*words ss ∧ ∃ suffix,r.2.val=out.val++suffix := by
 induction ss generalizing out with
 | nil => exact ⟨(.Ok (),out),rfl,Nat.le_refl _,by simp [words],[],by simp⟩
 | cons s ss ih =>
   have count : words (s::ss)=s.length+words ss := by simp [words]
   rw [count] at cap ⊢
   obtain ⟨⟨status,mid⟩,call,lo,hi,suffix,prior⟩:=NHG_FieldBounds.source out s (by change out.val.length+4*s.length≤Usize.max;omega)
   change out.val.length≤mid.val.length at lo
   change mid.val.length≤out.val.length+4*s.length at hi
   change mid.val=out.val++suffix at prior
   cases status with
   | Err e =>
     refine ⟨(.Err e,mid),?_,lo,(by change mid.val.length≤out.val.length+4*(s.length+words ss);omega),suffix,prior⟩
     simp only [chain,call,thenCheck,bind_tc_ok];rfl
   | Ok u =>
     obtain ⟨r,next,lo',hi',tail,frame⟩:=ih mid (by omega)
     refine ⟨r,?_,by omega,by omega,suffix++tail,?_⟩
     · simp only [chain,call,thenCheck,bind_tc_ok];change chain ss mid=ok r;exact next
     · rw [frame,prior,List.append_assoc]

theorem map_chain (ss : List (Slice U32)) (out : ByteVec) :
 mapPairOutcome (chain ss out)=AspisR1PublicSerializer.Frontier431.chain ss out := by
 induction ss generalizing out with
 | nil => rfl
 | cons s ss ih =>
   simp only [chain,AspisR1PublicSerializer.Frontier431.chain]
   rw [SerializerLoop.fields_eq]
   simp only [NHG_FieldSpec.fields]
   cases h : pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields out s with
   | fail e => rfl
   | div => rfl
   | ok pair =>
     rcases pair with ⟨status,mid⟩
     cases status with
     | Err e => rfl
     | Ok u => cases u;exact ih mid

theorem map_injective (a b : Result (Status × ByteVec))
 (h : mapPairOutcome a=mapPairOutcome b) : a=b := by
 cases a with
 | fail e => cases b <;> cases h <;> rfl
 | div => cases b <;> cases h <;> rfl
 | ok a =>
   cases b with
   | fail e => cases h
   | div => cases h
   | ok b =>
     have eq:=Result.ok.inj h
     have status:=NHG_FieldSpec.status_injective a.1 b.1 (congrArg Prod.fst eq)
     have vec:=congrArg Prod.snd eq
     exact congrArg Result.ok (Prod.ext status vec)

/-- Complete emitted twenty-callee composition, including the exact error and
Vec at the first rejecting child. No child-success premise. -/
theorem source (out : ByteVec) (values : Array (Array U32 8#usize) 20#usize) :
 pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier out values =
 chain (AspisR1PublicSerializer.Frontier431.rows values) out := by
 apply map_injective
 rw [←SerializerWhole.frontier_eq,AspisR1PublicSerializer.Frontier431.frontier_eq_chain]
 exact (map_chain _ _).symm

theorem row_length (values : Array (Array U32 8#usize) 20#usize) (i : Fin 20) :
 (AspisR1PublicSerializer.Frontier431.row values i).length=8 := by
 unfold AspisR1PublicSerializer.Frontier431.row
 exact (values.val[i.val]'(by simpa [values.property] using i.isLt)).property

theorem row_count (values : Array (Array U32 8#usize) 20#usize) :
 words (AspisR1PublicSerializer.Frontier431.rows values)=160 := by
 simp only [words,AspisR1PublicSerializer.Frontier431.rows,List.map_cons,List.map_nil,
  List.sum_cons,List.sum_nil,row_length]
 rfl

theorem stage_domain (initial current row : Nat) (start : 1≤ initial ∧ initial≤1240)
 (progress : initial≤ current ∧ current≤ initial+32*row) (index : row<20) :
 1≤ current ∧ current≤1240+32*row ∧ current+32≤1880 := by omega

theorem frontier_envelope (out : ByteVec) (values : Array (Array U32 8#usize) 20#usize)
 (cap : out.val.length+640≤Usize.max) :
 ∃ r,pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier out values=ok r ∧
 out.val.length≤r.2.val.length ∧ r.2.val.length≤out.val.length+640 ∧
 ∃ suffix,r.2.val=out.val++suffix := by
 rw [source]
 have h:=envelope (AspisR1PublicSerializer.Frontier431.rows values) out
 rw [row_count] at h
 exact h cap

#print axioms row_length
#print axioms row_count
#print axioms stage_domain
#print axioms frontier_envelope
#print axioms envelope
#print axioms map_chain
#print axioms map_injective
#print axioms source
end AspisR1.NHG_FrontierFrame
