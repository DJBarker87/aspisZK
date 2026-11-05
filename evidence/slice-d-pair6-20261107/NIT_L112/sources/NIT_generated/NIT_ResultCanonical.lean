import NIT_AllocatorChain
set_option autoImplicit false
namespace AspisR1.NIT_ResultCanonical
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl

def Canonical (out : Result NR) : Prop :=
 match out with | .ok (.Ok x)=>canonE x | _=>True

theorem final (parts : Parts) (kappa : E) (out : Result NR)
 (trace : NIT_TailPhases.Final parts kappa out) : Canonical out := by
 cases trace with
 | returned powers sum out powersLaw trace cut =>
  rcases cut with ⟨canonical,rfl⟩
  exact canonical

theorem libra (f : Ref (Slice U8)) (weights : Powers) (parts : Parts) (kappa : E) (out : Result NR)
 (trace : NIT_TailPhases.Libra f weights parts kappa out) : Canonical out := by
 cases trace with
 | failed e trace => trivial
 | diverged trace => trivial
 | returned after out trace tail => exact final after kappa out tail

theorem group (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells) (ap0 ap1 : Ref Powers)
 (parts : Parts) (kappa : E) (out : Result NR)
 (trace : NIT_TailPhases.Group w f low ap0 ap1 parts kappa out) : Canonical out := by
 cases trace with
 | failed e call => trivial
 | diverged call => trivial
 | returned l after out cut call factor tail => exact libra f l.libra_reply after kappa out tail

theorem tail (w : Ref W) (f : Ref (Slice U8)) (ap0 ap1 : Ref Powers) (parts : Parts)
 (kappa : E) (address : Nat) (out : Result NR)
 (trace : NIT_TailChain.Trace w f ap0 ap1 parts kappa address out) : Canonical out := by
 cases trace with
 | low cells out trace rest => exact group w f ⟨address,cells⟩ ap0 ap1 parts kappa out rest

theorem high (c : Context) (w : Ref W) (parts : Parts) (reply : RU) (out : Result NR)
 (trace : NIT_SharedChain.High c w parts reply out) : Canonical out := by
 cases trace with
 | rejected e => trivial
 | returned out rest => exact tail w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress out rest

theorem partial_result (c : Context) (w : Ref W) (parts : Parts) (reply : RP) (out : Result NR)
 (trace : NIT_SharedChain.Partial c w parts reply out) : Canonical out := by
 cases trace with
 | rejected e => trivial
 | failed values e call => trivial
 | diverged values call => trivial
 | returned values reply after out call rest => exact high c w after reply out rest

theorem shared (c : Context) (parts : Parts) (out : Result NR)
 (trace : NIT_SharedChain.Shared c parts out) : Canonical out := by
 cases trace with
 | failed owner cells e common call => trivial
 | diverged owner cells common call => trivial
 | returned owner cells reply out common call rest => exact partial_result c ⟨c.w.address,owner⟩ parts reply out rest

theorem after (c : Context) (b : Bool) (parts : Parts) (reply : RU) (out : Result NR)
 (trace : NIT_RegularChain.After c b parts reply out) : Canonical out := by
 cases trace with
 | rejected e => trivial
 | unshared out isFalse rest => exact tail c.w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress out rest
 | shared out isTrue rest => exact shared c parts out rest

theorem regular [FIo_Native.Allocation] (c : Context) (scratch : Scratch) (out : Result NR)
 (trace : NIT_RegularChain.Trace c scratch out) : Canonical out := by
 cases trace with
 | failed e call => trivial
 | diverged call => trivial
 | returned reply scratch parts out call rest => exact after c _ parts reply out rest

theorem allocator (c : Context) (r : NP6_StdModel.Reservation) (out : Result NR)
 (trace : NIT_AllocatorChain.Trace c r out) : Canonical out := by
 cases trace with
 | rejected e => trivial
 | returned out rest =>
  letI:=FIo_Install.allocation (.Ok ())
  exact regular c _ out rest

#print axioms final
#print axioms libra
#print axioms group
#print axioms tail
#print axioms high
#print axioms partial_result
#print axioms shared
#print axioms after
#print axioms regular
#print axioms allocator
end AspisR1.NIT_ResultCanonical
