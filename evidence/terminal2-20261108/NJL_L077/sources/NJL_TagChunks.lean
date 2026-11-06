import NJL_TagChunk
import NJL_TagPartition
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_TagChunks
open Aeneas Aeneas.Std Result
open AspisV8R17.RawReducer (P)
open NJL_TagRawTrace (Selectors dot)
open NJL_TagReduction (State)
def run (s : Selectors) : List (List (Fin 272)) → State → Result State
 | [],before=>ok before
 | chunk::rest,before=>do
  let middle ← NJL_TagChunk.reference s chunk before
  run s rest middle
inductive Trace (s : Selectors) : List (List (Fin 272)) → State → State → Prop
 | nil (before : State) : Trace s [] before before
 | cons {chunk rest before middle after} (first : NJL_TagChunk.Invocation s chunk before middle)
   (tail : Trace s rest middle after) : Trace s (chunk::rest) before after
theorem dot_append (s : Selectors) (xs ys : List (Fin 272)) (i : Fin 4) :
 dot s (xs++ys) i=dot s xs i+dot s ys i := by simp only [dot,List.map_append,List.sum_append]
/-- Finite source chunk induction, preserving all four canonical output
limbs; neither a child success nor a final equality is a root input. -/
theorem source (s : Selectors) (chunks : List (List (Fin 272))) (before : State)
 (small : ∀ terms∈chunks,terms.length≤4) (hs : FIw_ArrayValue.canonical s.high) (hb : ∀ i,(before i).val<P) :
 ∃ after,run s chunks before=ok after ∧ Trace s chunks before after ∧
 (∀ i,(after i).val<P) ∧ (∀ i,(after i).val=((before i).val+dot s chunks.flatten i)%P) := by
 induction chunks generalizing before with
 | nil =>
  refine ⟨before,rfl,.nil before,hb,?_⟩
  intro i;simp only [List.flatten_nil,dot,List.map_nil,List.sum_nil,Nat.add_zero,Nat.mod_eq_of_lt (hb i)]
 | cons chunk rest ih =>
  obtain ⟨middle,cc,tc,hc,vc⟩ := NJL_TagChunk.source s chunk before (small _ (by simp)) hs hb
  obtain ⟨after,ca,ta,ha,va⟩ := ih middle (fun xs hx=>small xs (by simp [hx])) hc
  refine ⟨after,?_,.cons tc ta,ha,?_⟩
  · simp only [run,cc,bind_tc_ok,ca]
  · intro i
    rw [va i,vc i,List.flatten_cons,dot_append]
    simp only [Nat.add_mod,Nat.mod_mod,Nat.add_assoc]
#print axioms dot_append
#print source
#print axioms source
end AspisR1.NJL_TagChunks
end
