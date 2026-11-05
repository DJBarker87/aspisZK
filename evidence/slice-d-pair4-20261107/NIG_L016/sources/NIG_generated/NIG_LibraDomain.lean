import NIG_LibraWindow
import NIG_LoopPost
import NHM_LoopDomain
set_option autoImplicit false
namespace NIG_LibraDomain
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NIG_LibraLoop

def Inv (s:State):Prop:=s.1.end.val=4 ∧ s.1.start.val≤4 ∧ ∀x∈s.2.val,canonE x

theorem preserves (f:Slice U8) (libra:Libra) (hl:∀x∈libra.val,canonE x)
 (s t:State) (hs:Inv s) (run:body f libra s=ok (.cont t)):Inv t:=by
 obtain ⟨he,hi,active⟩:=progress f libra s t run
 have hev:=congrArg (fun x:Usize=>x.val) he
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases run
 | some j=>
  obtain ⟨out,ho,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  have same:=ControlFlow.cont.inj (Result.ok.inj run)
  have index:=(NHI_RangeProgress.some_next s.1 next j hn).1
  have small:j.val<4:=by rw [index];rcases hs with ⟨last,_,_⟩;omega
  have co:=NIG_LibraWindow.canonical f libra j s.2 out small hl hs.2.2 ho
  refine ⟨by omega,by omega,?_⟩
  rw [←same]
  exact co

theorem done (f:Slice U8) (libra:Libra) (s:State) (out:Cells)
 (hs:Inv s) (run:body f libra s=ok (.done out)):∀x∈out.val,canonE x:=by
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases ControlFlow.done.inj (Result.ok.inj run);exact hs.2.2
 | some j=>
  obtain ⟨out,ho,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  cases run

theorem all_calls (f:Slice U8) (libra:Libra) (hl:∀x∈libra.val,canonE x)
 (parts:Cells) (hp:∀x∈parts.val,canonE x):
 NHM_LoopDomain.all (body f libra) Inv 5 ({start:=0#usize,«end»:=4#usize},parts):=
 NHM_LoopDomain.invariant (body f libra) Inv (preserves f libra hl) 5 _ ⟨rfl,by decide,hp⟩

theorem source (f:Slice U8) (libra:Libra) (hl:∀x∈libra.val,canonE x)
 (parts out:Cells) (hp:∀x∈parts.val,canonE x)
 (run:FIo_Native.weights.Weights.pair_loop16 {start:=0#usize,«end»:=4#usize} f parts libra=ok out):
 ∀x∈out.val,canonE x:=by
 rw [NIG_LibraLoop.source] at run
 exact NIG_LoopPost.post (body f libra) Inv (fun out=>∀x∈out.val,canonE x)
  (preserves f libra hl) (done f libra) 5 _ out ⟨rfl,by decide,hp⟩ run
#print axioms preserves
#print axioms done
#print axioms all_calls
#print axioms source
end NIG_LibraDomain
