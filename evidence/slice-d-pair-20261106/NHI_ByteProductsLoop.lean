import NHI_CountedLoop
import NHI_RangeProgress
import NHE_DotDomain
set_option autoImplicit false
namespace NHI_ByteProductsLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1
abbrev Dot := NHE_DotState.Dot
abbrev Iter := core.ops.range.Range Usize
abbrev State := Iter × Dot
abbrev NQ := NHE_CheckedScalar.NQ
abbrev body (f : Slice U8) (scratch : Slice NQ) (s : State) :=
 FIo_Native.weights.push_byte_products_loop.body f scratch s.1 s.2

theorem progress (f : Slice U8) (scratch : Slice NQ) (s t : State)
 (run : body f scratch s=ok (.cont t)) :
 t.1.end=s.1.end ∧ t.1.start.val=s.1.start.val+1 ∧
 t.2.count.val=s.2.count.val+1 ∧ s.1.start.val<s.1.end.val := by
 unfold body FIo_Native.weights.push_byte_products_loop.body at run
 obtain ⟨⟨o,rest⟩,next,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none => cases run
 | some j =>
  obtain ⟨value,hv,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨scalar,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨⟨r,after⟩,hp,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases r with
  | Err e => cases run
  | Ok u =>
   cases u
   have same := ControlFlow.cont.inj (Result.ok.inj run)
   rw [←same]
   have index := NHI_RangeProgress.some_next s.1 rest j next
   exact ⟨index.2.1,index.2.2.1,NHE_DotDomain.push_count s.2 after value scalar hp,index.2.2.2⟩

theorem decreases (f : Slice U8) (scratch : Slice NQ) (s t : State)
 (run : body f scratch s=ok (.cont t)) :
 t.1.end.val-t.1.start.val<s.1.end.val-s.1.start.val := by
 obtain ⟨last,inc,count,more⟩ := progress f scratch s t run
 rw [last]
 omega

/-- Exact counted for-loop, including every failed field/read/push prefix.
This is Lean transport only; native wrapper qualification remains separate. -/
theorem source (f : Slice U8) (scratch : Slice NQ) (pair : Dot) (n : Usize) :
 FIo_Native.weights.push_byte_products pair f scratch n=
 NHI_CountedLoop.unroll (body f scratch) (n.val+1) ({start:=0#usize,«end»:=n},pair) := by
 unfold FIo_Native.weights.push_byte_products FIo_Native.weights.push_byte_products_loop
 exact NHI_CountedLoop.agrees (body f scratch) (fun s=>s.1.end.val-s.1.start.val)
  (decreases f scratch) (n.val+1) _ (by change n.val-0<n.val+1;omega)

#print axioms progress
#print axioms decreases
#print axioms source
end NHI_ByteProductsLoop
