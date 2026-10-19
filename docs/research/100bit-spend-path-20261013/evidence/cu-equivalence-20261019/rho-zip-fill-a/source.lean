import CuSavingsZipLoans
import CuSavingsSuffixOverwrite

/-! Concrete for/zip assignment using the original runtime Zip.next and
mutable-iterator handbacks packaged as loans. No new iterator axiom is used.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsZipFill
open Aeneas Aeneas.Std Result ControlFlow
open CuSavingsZipLoans CuSavingsSuffixOverwrite
variable {T U : Type}

theorem overwrite_set_before (n : Nat) (xs ys : List T) (hlen : xs.length = ys.length)
    (hn : n < ys.length) :
    overwrite (n+1) (xs.set n (ys[n]'hn)) ys = overwrite n xs ys := by
  induction n generalizing xs ys with
  | zero =>
    cases xs with
    | nil => cases ys <;> simp_all only [List.length_nil,List.length_cons]
    | cons x xs => cases ys with
      | nil => simp only [List.length_nil] at hn;omega
      | cons y ys => rfl
  | succ n ih =>
    cases xs with
    | nil => cases ys <;> simp_all only [List.length_nil,List.length_cons]
    | cons x xs => cases ys with
      | nil => simp only [List.length_nil] at hn;omega
      | cons y ys =>
        have hn' : n < ys.length := by omega
        have hl' : xs.length = ys.length := by simpa using hlen
        simpa only [overwrite,List.set_cons_succ,List.getElem_cons_succ] using
          congrArg (List.cons x) (ih xs ys hl' hn')

def body (f : U → Result T) (z : Zip T U) : Result (ControlFlow (Zip T U) (Zip T U)) := do
  let (item,next) ← zipNext z
  match item with
  | none => .ok (.done next)
  | some (loan,value) => do
    let replacement ← f value
    .ok (.cont {next with fst:=loan.write next.fst replacement})

def nextWritten (z : Zip T U) (replacement : T) : Zip T U :=
  {fst:={slice:=z.fst.slice.setAtNat z.fst.i replacement,i:=z.fst.i+1},
   snd:={z.snd with i:=z.snd.i+1}}

theorem step (f : U → Result T) (fn : U → T) (z : Zip T U)
    (hf : ∀ value,f value = .ok (fn value))
    (ha : z.fst.i < z.fst.slice.val.length) (hb : z.snd.i < z.snd.slice.val.length) :
    body f z = .ok (.cont (nextWritten z (fn (z.snd.slice.val[z.snd.i]'hb)))) := by
  have hlen : z.snd.slice.len.val = z.snd.slice.val.length := by
    simpa only [Slice.length] using Slice.len_val z.snd.slice
  have hb' : z.snd.i < z.snd.slice.len := by simpa only [hlen] using hb
  simp only [body,zipNext,
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    loanIterator,CuSavingsZipLoans.next_write z.fst ha,
    core.iter.traits.iterator.IteratorSliceIter,
    core.slice.iter.IteratorSliceIter.next,dif_pos hb',bind_tc_ok,hf]
  rfl

theorem done (f : U → Result T) (z : Zip T U)
    (ha : z.fst.slice.val.length ≤ z.fst.i) : body f z = .ok (.done z) := by
  simp only [body,zipNext,
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
    loanIterator,CuSavingsZipLoans.next_done z.fst ha,bind_tc_ok]
  rfl

theorem loop_success (fuel : Nat) (f : U → Result T) (fn : U → T) (z : Zip T U)
    (hf : ∀ value,f value = .ok (fn value))
    (hlen : z.fst.slice.val.length = z.snd.slice.val.length)
    (hpos : z.fst.i = z.snd.i)
    (hspan : z.fst.i+fuel = z.fst.slice.val.length) :
    ∃ last : Zip T U,loop (body f) z = .ok last ∧
      last.fst.slice.val = overwrite z.fst.i z.fst.slice.val (z.snd.slice.val.map fn) := by
  induction fuel generalizing z with
  | zero =>
    have hend : z.fst.i = z.fst.slice.val.length := by omega
    refine ⟨z,?_,?_⟩
    · rw [loop,done f z (by omega)]
    · rw [hend,overwrite_at_length _ _ (by simpa only [List.length_map] using hlen)]
  | succ fuel ih =>
    have ha : z.fst.i < z.fst.slice.val.length := by omega
    have hb : z.snd.i < z.snd.slice.val.length := by omega
    let replacement := fn (z.snd.slice.val[z.snd.i]'hb)
    let next := nextWritten z replacement
    have hnextlen : next.fst.slice.val.length = z.fst.slice.val.length := by
      simp only [next,nextWritten,Slice.setAtNat,List.length_set]
    obtain ⟨last,hrun,hvalues⟩ := ih next
      (by simpa only [next,nextWritten,hnextlen] using hlen)
      (by simp only [next,nextWritten,hpos])
      (by change z.fst.i+1+fuel = _;rw [hnextlen];omega)
    refine ⟨last,?_,?_⟩
    · rw [loop,step f fn z hf ha hb]
      exact hrun
    · rw [hvalues]
      have htarget : (z.snd.slice.val.map fn)[z.fst.i]'(by simpa only [List.length_map] using (hpos ▸ hb)) = replacement := by
        simp only [List.getElem_map,replacement,hpos]
      change overwrite (z.fst.i+1) (z.fst.slice.val.set z.fst.i replacement)
        (z.snd.slice.val.map fn) = _
      rw [← htarget]
      exact overwrite_set_before z.fst.i _ _ (by simpa only [List.length_map] using hlen) _

def fill (f : U → Result T) (raw : Slice T) (weights : Slice U) : Result (Slice T) := do
  let last ← loop (body f) ⟨{slice:=raw},{slice:=weights,i:=0}⟩
  .ok last.fst.slice

theorem fill_success (f : U → Result T) (fn : U → T) (raw : Slice T) (weights : Slice U)
    (hf : ∀ value,f value = .ok (fn value)) (hlen : raw.val.length = weights.val.length) :
    fill f raw weights = .ok ⟨weights.val.map fn,by
      simpa only [List.length_map] using weights.property⟩ := by
  let z : Zip T U := ⟨{slice:=raw},{slice:=weights,i:=0}⟩
  obtain ⟨last,hrun,hvalues⟩ := loop_success raw.val.length f fn z hf hlen rfl (by simp only [z,Nat.zero_add])
  unfold fill
  rw [hrun]
  simp only [bind_tc_ok]
  apply congrArg Result.ok
  apply Subtype.ext
  exact hvalues

#print axioms step
#print axioms done
#print axioms loop_success
#print axioms fill_success
end AspisR1.CuSavingsZipFill
