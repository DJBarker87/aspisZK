import JFm_BlockSplit
set_option autoImplicit false
namespace AspisR1.JGe_ValuesAssembly
open Aeneas Aeneas.Std

theorem source (xs : List (List U8)) (lengths : ∀ c∈xs,c.length=16) :
    JFw_Blocks.blocks xs.length xs.flatten=
      xs.map (fun c => c ++ List.replicate 16 0#u8) := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    have hc := lengths c (List.mem_cons_self ..)
    have hs : ∀ s∈cs,s.length=16 := fun s h => lengths s (List.mem_cons_of_mem c h)
    simp only [List.length_cons,List.flatten_cons]
    rw [show cs.length+1=1+cs.length by omega]
    rw [JFm_BlockSplit.append 1 cs.length c cs.flatten (by simpa using hc),ih hs]
    simp only [JFw_Blocks.blocks,List.take_of_length_le (by omega : c.length≤16),
      List.map_cons,List.cons_append,List.nil_append]
#print axioms source
end AspisR1.JGe_ValuesAssembly
