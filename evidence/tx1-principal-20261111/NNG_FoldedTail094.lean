import NNG_BatchTail094
import NNG_FoldedCopy094
import NNG_BatchDomain094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FoldedTail094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136 NNG_Carriers094

theorem source (env : RSL.Env) (s : NNG_Context094.Parent Unit)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (input : LIBC_PreparedLaw.Args) (ep ea : List RSL.Event)
 (observer : s.observer=none) (split : s.k.val=10)
 (prepared : LIBC_PreparedLaw.law input env ⟨.ret (.ok (toT12 p),arr toT3 g),ep⟩)
 (fields : NGC_PreparationBoundary.Fields (NFW_PreparedPort.prepared (toT12 p)))
 (initial : LIBC_AccNew.child.run () env ⟨.ret (.ok (toT15 a)),ea⟩)
 (proofWidth : (LIB_Carriers.bytes s.proof).length=57607)
 (publicWidth : (LIB_Carriers.bytes s.publicBytes).length=1880)
 (root0 root1 : Array U8 32#usize)
 (roots : (toT12 p).roots=Array.make 2#usize [root0,root1])
 (first : root0.val=(s.proof.val.drop 16).take 32) :
 NNG_Reference094.afterNew s (toT12 p) (arr toT3 g) (toT15 a) env
  (observation NNG_Producer094.port (NNG_Events094.events env)
   (NNG_Tree094.f_i (NNG_InstalledCalls094.calls env) s g p a)) := by
 have width : s.proof.val.length=57607 := by
  rw [NMS_R2N_RSLScalars.bytes_length] at proofWidth
  exact proofWidth
 let folded := NNG_FoldedCopy094.root s.proof width
 have queries := NNG_PreparedQueries094.returned input env (toT12 p) (arr toT3 g) ep prepared
 have domain := NNG_BatchDomain094.reached s.proof (toT12 p) folded root0 root1 width queries.2 roots first
  (NNG_FoldedCopy094.exact_bytes s.proof width)
 unfold NNG_Reference094.afterNew
 rw [NNG_FoldedCopy094.reference s.proof width]
 have tail := NNG_BatchTail094.source env s p a g folded input ep ea observer split prepared fields initial
  proofWidth publicWidth domain
 exact Eq.mp (congrArg (NNG_Reference094.batch s (toT12 p) (arr toT3 g) (toT15 a) (LIB_Carriers.b32 folded) env)
  (NNG_FoldedCopy094.source env s g p a width).symm) tail
#print axioms source
end AspisR1.NNG_FoldedTail094
