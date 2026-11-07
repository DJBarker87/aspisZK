import NNG_ModelRoot136
import NNG_Erasure137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ReturnedPath137
open Aeneas Aeneas.Std Result NMP_prepare NNG_Context137

def public_ {H : Type} (c : Calls) (s : Parent H) (p : r1_wire.Prefix) : Result (Output H) := do
 let r←c.publicTranscript s.digest s.publicValue s.hash p.c1_root
 match r with
 | .Err e=>ok (.Err e)
 | .Ok t=>
   let (r,after)←c.begin_ s.digest p t
   match r with
   | .Err e=>ok (.Err e)
   | .Ok ch=>do
     c.mark s.observer 1#u8
     c.finish s.digest s.publicValue p after ch s.observer

def tree {H : Type} (c : Calls) (s : Parent H) : Result (Output H) := do
 let r←c.parse s.bytes
 match r with
 | .Err e=>ok (.Err e)
 | .Ok p=>do
   c.mark s.observer 0#u8
   public_ c s p

theorem source {H : Type} (c : Calls) (s : Parent H) : tree c s=emitted c s := by
 rw [←NNG_Erasure137.source]
 simp only [NNG_Tree137.tree,NNG_Tree137.mark0,NNG_Tree137.publicTranscript,
   NNG_Tree137.begin_,NNG_Tree137.mark1,NNG_Tree137.finish,NMT_CallTree.erase_bind,
   NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,Bind.bind]
 rfl
#print axioms source

theorem returned (env : RSL.Env) (s : Parent Unit) (out : r1_semantic.Verified Unit)
 (native : emitted (calls env) s=.ok (.Ok out)) :
 ∃ p t ch after,
 NMP_Install138.parse s.bytes=.ok (.Ok p) ∧
 NMP_Install131.publicTranscript s.digest s.publicValue s.hash p.c1_root=.ok (.Ok t) ∧
 NMP_Install150.begin_ s.digest p t=.ok (.Ok ch,after) ∧
 NNG_FinishAdapter137.call env s.digest s.publicValue p after ch s.observer=.ok (.Ok out) := by
 rw [←source] at native
 unfold tree at native
 obtain ⟨reply,parsed,tail⟩:=NNG_ModelSuccess136.bind_out _ _ _ native
 cases reply with
 | Err e=>cases tail
 | Ok p=>
   simp only [calls,bind_tc_ok] at tail
   unfold public_ at tail
   obtain ⟨reply,publicCall,tail⟩:=NNG_ModelSuccess136.bind_out _ _ _ tail
   cases reply with
   | Err e=>cases tail
   | Ok t=>
     obtain ⟨⟨reply,after⟩,begun,tail⟩:=NNG_ModelSuccess136.bind_out _ _ _ tail
     cases reply with
     | Err e=>cases tail
     | Ok ch=>
       simp only [calls,bind_tc_ok] at tail
       exact ⟨p,t,ch,after,parsed,publicCall,begun,tail⟩
#print axioms returned
end AspisR1.NNG_ReturnedPath137
