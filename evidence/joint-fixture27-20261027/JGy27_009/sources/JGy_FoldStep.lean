import JFp_SHABlocks
set_option autoImplicit false
namespace AspisR1.JGy_FoldStep
open JFp_SHA256

/-- One certified round, with the rest of the schedule passed symbolically. -/
theorem step (k : Nat) (ks w next : List Nat) (s after out : Reg)
    (word : advance w=next) (round : JFp_SHA256.round s k (w.getD 0 0)=after)
    (rest : (ks.foldl transition (next,after)).2=out) :
    ((k::ks).foldl transition (w,s)).2=out := by
  simpa only [List.foldl_cons,transition,word,round] using rest

/-- Transfer a compact schedule certificate through the final feed-forward. -/
theorem compression (input w : List Nat) (start last result : Reg)
    (parsed : words input=w) (run : (constants.foldl transition (w,start)).2=last)
    (feed : add start last=result) : compress start (words input)=result := by
  rw [parsed,compress,loop,run,feed]

#print axioms step
#print axioms compression
end AspisR1.JGy_FoldStep
