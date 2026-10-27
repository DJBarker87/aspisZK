import JFr_TX2_Powers
import FIp_DotsAdapter
import JFr_TX2_Scalars
import JFr_TX2_DotLaneTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_FirstLane
open Aeneas Aeneas.Std Result

def native : Array FIo_Install.NE 29#usize := FIp_DotsAdapter.toArray JFr_TX2_Powers.value

def coefficient (term : Fin 26) : FIo_Install.NE :=
  FIo_Install.toE (JFr_TX2_Powers.value.val[term.val]'(by rw [JFr_TX2_Powers.value.property];have:=term.isLt;omega))

def limbs (term : Fin 26) : Array U32 8#usize :=
  let x:=coefficient term
  Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
    x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]

theorem source (i : Fin 12) (slot : Fin 4) (term : Fin 26) :
    ∃ out : U64,
      JFr_TX2_DotLanes.lane (limbs term)
        ((JFr_TX2_Scalars.values i slot).val[term.val]'(by rw [(JFr_TX2_Scalars.values i slot).property];exact term.isLt))
        (Array.repeat 8#usize 0#u64) 0#usize=
        ok ((Array.repeat 8#usize 0#u64).set 0#usize out) ∧
      out.val=(coefficient term).c0.c0.a.val*
        ((JFr_TX2_Scalars.values i slot).val[term.val]'(by rw [(JFr_TX2_Scalars.values i slot).property];exact term.isLt)).val := by
  have canon := JFr_TX2_Powers.canonical ⟨term.val,by have:=term.isLt;omega⟩
  have hw : (coefficient term).c0.c0.a.val<JFr_TX2_DotBounds.P := canon.1.1.1
  obtain ⟨out,run,value,_⟩ := JFr_TX2_DotLaneTotal.source (limbs term)
    ((JFr_TX2_Scalars.values i slot).val[term.val]'(by rw [(JFr_TX2_Scalars.values i slot).property];exact term.isLt))
    (coefficient term).c0.c0.a (Array.repeat 8#usize 0#u64) 0#usize 0#u64 0
    (by decide) rfl rfl hw (JFr_TX2_Scalars.canonical i slot term) (by omega) (by simp)
  exact ⟨out,run,by simpa only [show (0#u64).val=0 from rfl,Nat.zero_add] using value⟩

#print axioms source
end AspisR1.JFr_TX2_FirstLane
end
