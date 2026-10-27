import XRs_AddInvariant
import XRs_LoopBind
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XRs_AddLoop
open XRs_AddStep XRs_AddIndexed XRs_AddInvariant
abbrev ebody (s : Iter × Back × U32) :=
 XRn_Join_Release.sampler.add_small_base_p_loop.body s.1 s.2.1 s.2.2
abbrev ibody (s : Array U32 8#usize × U32 × Usize) :=
 AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p_loop.body s.1 s.2.1 s.2.2

def output (seed : Array U32 8#usize) (base : Iter) (p : U32 × Back) :
 Result (Array U32 8#usize × U32) := ok (Array.from_slice seed (p.2 base).slice,p.1)

theorem restored (seed a : Array U32 8#usize) (base : Iter) (back : Back)
 (i : Nat) (g : Good base back a i) (c : U32) : output seed base (c,back) = ok (a,c) := by
 unfold output Array.from_slice
 have hlen : (back base).slice.val.length = (8#usize).val := g.restored ▸ a.property
 rw [dif_pos hlen]
 congr 2
 exact Subtype.ext g.restored

theorem right {T : Type} (r : Result T) : (r >>= fun x => ok x) = r := by cases r <;> rfl

theorem join (seed : Array U32 8#usize) (base : Iter)
 (hlen : base.slice.val.length = 8) (n i : Nat) (bound : i+n=8)
 (a : Array U32 8#usize) (back : Back) (c : U32) (g : Good base back a i) :
 (loop ebody ({base with i:=i},back,c) >>= output seed base) =
 loop ibody (a,c,idx i (by omega)) := by
 induction n generalizing i a back c with
 | zero =>
   have hi : i=8 := by omega
   subst i
   have he : ebody ({base with i:=8},back,c) = ok (.done (c,back)) :=
    exhausted _ _ _ (by simpa only [hlen] using (Nat.lt_irrefl 8))
   rw [XRs_LoopBind.done ebody _ _ _ he,restored seed a base back 8 g c]
   rw [loop.eq_def]
   rfl
 | succ n ih =>
   have hi : i<8 := by omega
   have hb : i<base.slice.val.length := by omega
   have ha : i<a.val.length := by have h := a.property; change a.val.length=8 at h; omega
   have hv : base.slice.val[i] = a.val[i] := by
    have h := g.suffix i (by omega)
    rw [List.getElem?_eq_getElem ha,List.getElem?_eq_getElem hb] at h
    exact (Option.some.inj h).symm
   have he : ebody ({base with i:=i},back,c) =
    (step a.val[i] c >>= fun p => ok (.cont ({base with i:=i+1},fun r => back (write r i p.1),p.2))) := by
    unfold ebody
    rw [emitted ({base with i:=i}) back c hb]
    simp only [hv]
    apply congrArg (fun k => step a.val[i] c >>= k)
    funext p
    cases p
    rfl
   rw [XRs_LoopBind.step ebody _ _ _ _ he]
   have hiStep := body a c i hi
   have hI : (loop ibody (a,c,idx i (by omega))) =
    (step a.val[i] c >>= fun p => loop ibody (set a i p.1,p.2,idx (i+1) (by omega))) := by
    have h := XRs_LoopBind.step ibody (a,c,idx i (by omega))
      (step a.val[i] c) (fun p => (set a i p.1,p.2,idx (i+1) (by omega))) (fun x => ok x) hiStep
    simpa only [right] using h
   rw [hI]
   apply congrArg (fun k => step a.val[i] c >>= k)
   funext p
   exact ih (i+1) (by omega) (set a i p.1) (fun r => back (write r i p.1)) p.2
    (advance base back a i p.1 g)
#print axioms restored
#print axioms right
#print axioms join
end XRs_AddLoop
