import NLL_ParentInvocation
set_option autoImplicit false
noncomputable section
namespace LIBC_BatchWire
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- The returned root and execution history use the supplied roots, not the
parsed semantic rows. Only SAME wire bytes select the leaf preimages. -/
theorem leaf (p q : OraclePortCompactDraft.Parsed) (wire : p.wire=q.wire) (kind pos : Nat) :
 OraclePortSelectedDraft.leaf p kind pos=OraclePortSelectedDraft.leaf q kind pos := by
 simp only [OraclePortSelectedDraft.leaf,OraclePortSelectedDraft.opening,wire]
theorem build (H : Bytes → State) (p q : OraclePortCompactDraft.Parsed) (wire : p.wire=q.wire)
 (queries : Fin 22 → Fin 262144) (kind : Nat) (positions : List Nat) (s : reference.Scratch) :
 NKV_LeafBuild.build H p queries kind positions s=NKV_LeafBuild.build H q queries kind positions s := by
 induction positions generalizing s with
 | nil => rfl
 | cons pos rest ih =>
   simp only [NKV_LeafBuild.build,leaf p q wire]
   cases reference.leaf_step s (MultiproofConeLeafFold.key queries kind pos)
    (AspisV8R19.SqueezeOracleBridge.encodeState (H (OraclePortSelectedDraft.leaf q kind pos))) with
   | fail e => rfl
   | div => rfl
   | ok out => cases out with
     | none => rfl
     | some t => rw [ih t]
theorem query_plan (H : Bytes → State) (p q : OraclePortCompactDraft.Parsed) (wire : p.wire=q.wire)
 (queries : Fin 22 → Fin 262144) (batch kind : Nat) (nodes : Slice U8) (root : NLL.Root) (s : reference.Scratch) :
 NKV_QueryPlan.plan H p queries batch kind nodes root s=NKV_QueryPlan.plan H q queries batch kind nodes root s := by
 unfold NKV_QueryPlan.plan
 rw [build H p q wire]
theorem plan (H : Bytes → State) (proof : Slice U8) (p q : OraclePortCompactDraft.Parsed) (wire : p.wire=q.wire)
 (raw : Array U32 22#usize) (batch : Usize) (sites : List Call) (idx : NLL.Indices) (val : NLL.Values) :
 NLL_Parent.plan H proof p raw batch sites idx val=NLL_Parent.plan H proof q raw batch sites idx val := by
 induction sites generalizing idx val with
 | nil => rfl
 | cons site rest ih =>
   rcases site with ⟨root,kind⟩
   simp only [NLL_Parent.plan,query_plan H p q wire]
   cases NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H)
    (NKV_ConcreteChildren.digest H) proof raw root batch kind idx val () with
   | fail e => rfl
   | div => rfl
   | ok out => rcases out with ⟨r,i,v⟩;cases r with
     | Err e => rfl
     | Ok u => rw [ih i v]
#print axioms leaf
#print axioms build
#print axioms query_plan
#print axioms plan
end LIBC_BatchWire
