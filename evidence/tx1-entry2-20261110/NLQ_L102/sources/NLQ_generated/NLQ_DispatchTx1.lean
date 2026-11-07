import NLQ_ByteDispatch
set_option autoImplicit false
noncomputable section
namespace NLQ_DispatchTx1
open Aeneas Aeneas.Std Result AspisR1 NLQ_DispatchState
/-- Native-cut G on TX1: the child's complete returned error/abort/result,
post-world and internal attempted prefix are forwarded at SAME arguments.
All non-TX1 children remain arbitrary; none is used as a stand-in. -/
theorem ten {A F C : Type} (children : Children A F C) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (world : F) :
 process children p a NJD_Prefixes.ten world =
 prepend [.head world NJD_Prefixes.ten (.ok (some 3#u8)),
  .copied world (some 3#u8) (.ok (some 3#u8)),
  .eq world NJD_Prefixes.ten (Array.make 2#usize [3#u8,10#u8]) (.ok true)]
  (invoke children.first p a NJD_Prefixes.ten world) := by
 simp [process,fallback,step,prepend,Hiq_DispatchSource.firstByte,Hiq_DispatchSource.copied,
  Hiq_DispatchSource.eqU8,NJD_Prefixes.ten,Array.make]
 all_goals simp only [NLQ_ByteDispatch.three]
 all_goals rfl
theorem eleven {A F C : Type} (children : Children A F C) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (world : F) :
 process children p a NJD_Prefixes.eleven world =
 prepend [.head world NJD_Prefixes.eleven (.ok (some 3#u8)),
  .copied world (some 3#u8) (.ok (some 3#u8)),
  .eq world NJD_Prefixes.eleven (Array.make 2#usize [3#u8,10#u8]) (.ok false),
  .eq world NJD_Prefixes.eleven (Array.make 2#usize [3#u8,11#u8]) (.ok true)]
  (invoke children.first p a NJD_Prefixes.eleven world) := by
 simp [process,fallback,step,prepend,Hiq_DispatchSource.firstByte,Hiq_DispatchSource.copied,
  Hiq_DispatchSource.eqU8,NJD_Prefixes.eleven,Array.make]
 all_goals simp only [NLQ_ByteDispatch.three]
 all_goals rfl
theorem complete {A F C : Type} (children : Children A F C) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (d : Slice U8) (world : F) (tx1 : NLQ_Route.Tx1 d) :
 ((process children p a d world).result,(process children p a d world).post)=
 ((children.first p a d world).result,(children.first p a d world).post) := by
 rcases tx1 with h | h
 · have eq : d=NJD_Prefixes.ten := Subtype.ext h
   subst d; rw [ten]; rfl
 · have eq : d=NJD_Prefixes.eleven := Subtype.ext h
   subst d; rw [eleven]; rfl
#print ten
#print eleven
#print complete
#print axioms ten
#print axioms eleven
#print axioms complete
end NLQ_DispatchTx1
