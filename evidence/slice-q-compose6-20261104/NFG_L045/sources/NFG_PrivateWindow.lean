import NFG_ArrayWindow
import NFE_NFC_DotPushFour
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFG_PrivateWindow
open Aeneas Aeneas.Std Result ControlFlow
abbrev Dot := FIo_Native.fast_pairing.canonical.Dot
abbrev Raw := Array U64 4#usize
abbrev update := NFE_NFC_DotPushFour.update

def index (i : Fin 4) : Usize := Usize.ofNat i.val (by have:=i.isLt;scalar_tac)
def next (i : Fin 4) : Usize := Usize.ofNat (i.val+1) (by have:=i.isLt;scalar_tac)
def output (self : Dot) (raw : Raw) (i : Fin 4) : Dot :=
 ⟨self.sums.set (index i) (update self.sums.val[i.val]! raw.val[i.val]!)⟩
/-- Exact statement asserted by the arbitrary observed native window, with
all other coordinates framed, on the SAME receiver and raw result. -/
def Window (before after : Dot) (raw : Raw) (i : Fin 4) : Prop := ∀ k : Fin 4,
 after.sums.val[k.val]! = if k.val=i.val then update before.sums.val[k.val]! raw.val[k.val]!
  else before.sums.val[k.val]!

theorem window (before after : Dot) (raw : Raw) (i : Fin 4)
 (observed : Window before after raw i) : after=output before raw i := by
 obtain ⟨a,b,c,d,hs⟩ := NFC_ArrayFour.shape before.sums
 rcases before with ⟨sums⟩
 dsimp only at hs
 subst sums
 rcases after with ⟨after⟩
 apply congrArg FIo_Native.fast_pairing.canonical.Dot.mk
 apply NFG_ArrayWindow.ext
 intro k
 have h:=observed k
 fin_cases i <;> fin_cases k <;>
  simpa [Window,output,index,Array.set,Array.make] using h

/-- Native window association to the actual emitted one-iteration Result. -/
theorem step (before after : Dot) (raw : Raw) (i : Fin 4)
 (observed : Window before after raw i) :
 FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw
  {start:=index i,«end»:=4#usize} before =
 ok (cont ({start:=next i,«end»:=4#usize},after)) := by
 rw [window before after raw i observed]
 obtain ⟨a,b,c,d,hs⟩ := NFC_ArrayFour.shape before.sums
 obtain ⟨r0,r1,r2,r3,hr⟩ := NFC_ArrayFour.shape raw
 rcases before with ⟨sums⟩
 dsimp only at hs
 subst sums
 subst raw
 fin_cases i <;>
  exact NFE_NFC_DotPushStep.source _ _ _ _ _ _ (by decide)
   (JGo_TX2_Range.next _ _ _ (by decide) (by decide)) rfl rfl
#print axioms window
#print axioms step
end AspisR1.NFG_PrivateWindow
end
