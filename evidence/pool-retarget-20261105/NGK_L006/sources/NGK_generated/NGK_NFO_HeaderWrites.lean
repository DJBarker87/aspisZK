import Lean
import S6AfterstateWriteFramesV1

set_option autoImplicit false
namespace NGK_NFO_HeaderWrites

theorem header {T : Type} (magic : List T) (width : magic.length = 4)
    (n : Nat) (zero a b c d : T) :
    (((((List.replicate (n+8) zero).setSlice! 0 magic).set 4 a).set 5 b).set 6 c).set 7 d =
      (magic ++ [a,b,c,d]) ++ List.replicate n zero := by
  have h0 := AspisS6SliceFrame.setSlice_append_chunk [] magic (n+8) zero (by rw [width]; omega)
  simp only [List.length_nil,List.nil_append,width,show n+8-4=n+4 by omega] at h0
  rw [h0]
  have h1 := AspisS6SliceFrame.set_append_point magic (n+3) zero a
  simp only [width] at h1
  rw [h1]
  have h2 := AspisS6SliceFrame.set_append_point (magic++[a]) (n+2) zero b
  simp only [List.length_append,List.length_cons,List.length_nil,width,Nat.reduceAdd] at h2
  rw [h2]
  have h3 := AspisS6SliceFrame.set_append_point (magic++[a]++[b]) (n+1) zero c
  simp only [List.length_append,List.length_cons,List.length_nil,width,Nat.reduceAdd] at h3
  rw [h3]
  have h4 := AspisS6SliceFrame.set_append_point (magic++[a]++[b]++[c]) n zero d
  simp only [List.length_append,List.length_cons,List.length_nil,width,Nat.reduceAdd] at h4
  rw [h4]
  simp only [List.append_assoc,List.cons_append,List.nil_append,List.singleton_append]
#print axioms header
end NGK_NFO_HeaderWrites

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
