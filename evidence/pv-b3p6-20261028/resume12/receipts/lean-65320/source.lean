import PV_B3P_ArrayWrite227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std
set_option autoImplicit false

def four_stores12 {α : Type} (zero a b c d : α) : Result (Array α 4#usize) := do
  let s0 ← Array.update (Array.repeat 4#usize zero) 0#usize a
  let s1 ← Array.update s0 1#usize b
  let s2 ← Array.update s1 2#usize c
  Array.update s2 3#usize d

theorem four_stores_value12 {α : Type} (zero a b c d : α) :
    four_stores12 zero a b c d =
      .ok (Array.make 4#usize [a,b,c,d] (by decide)) := by
  unfold four_stores12
  rw [PV_B3P_ArrayWrite227.update _ 0#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_ArrayWrite227.update _ 1#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_ArrayWrite227.update _ 2#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_ArrayWrite227.update _ 3#usize (by decide)]
  rfl

def four_build12 {α : Type} (read : Usize → Result α) : Result (Array α 4#usize) := do
  let a ← read 0#usize
  let b ← read 1#usize
  let c ← read 2#usize
  let d ← read 3#usize
  .ok (Array.make 4#usize [a,b,c,d] (by decide))

theorem four_interleaved12 {α : Type} (zero : α) (read : Usize → Result α) :
    (do
      let a ← read 0#usize
      let s0 ← Array.update (Array.repeat 4#usize zero) 0#usize a
      let b ← read 1#usize
      let s1 ← Array.update s0 1#usize b
      let c ← read 2#usize
      let s2 ← Array.update s1 2#usize c
      let d ← read 3#usize
      Array.update s2 3#usize d) = four_build12 read := by
  unfold four_build12
  apply congrArg (fun f => read 0#usize >>= f)
  funext a
  rw [PV_B3P_ArrayWrite227.update _ 0#usize (by decide)]
  simp only [bind_tc_ok]
  apply congrArg (fun f => read 1#usize >>= f)
  funext b
  rw [PV_B3P_ArrayWrite227.update _ 1#usize (by decide)]
  simp only [bind_tc_ok]
  apply congrArg (fun f => read 2#usize >>= f)
  funext c
  rw [PV_B3P_ArrayWrite227.update _ 2#usize (by decide)]
  simp only [bind_tc_ok]
  apply congrArg (fun f => read 3#usize >>= f)
  funext d
  rw [PV_B3P_ArrayWrite227.update _ 3#usize (by decide)]
  rfl

#print axioms four_interleaved12
#print axioms four_stores_value12
end PV_B3P_Binding12227
