import NMV_NoWrite241
set_option autoImplicit false
namespace NMV_G2Reference
open RSL NMV_NoWrite NMV_NoWriteSdk NMV_NoWrite241

theorem reference_free (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (pl : PoolLaws L) (hw : ∀ p q r, Free (V.tx2auth p q r))
 (a : TX2_240.Args) (s : SdkState) : Free (TX2_240.Ref L D V a s) := by
 unfold TX2_240.Ref
 split
 · exact pure_free _
 · apply bind_free
   · apply emit_free; intro c b h; cases h
   · intro _
     apply bind_free _ _ (snapshots_free _ _ s)
     intro r
     apply bind_free _ _ (env_free _)
     intro clock
     apply bind_free
     · apply emit_free; intro c b h; cases h
     · intro _
       apply bind_free
       · exact call_free _ _ _ (owned241_free L D V pl hw _)
       · intro _; exact pure_free _

/-- The entire G2 reference clause, including stopped prefixes. Library
write-freeness is an explicit CLOSED-child boundary, never an own-input clause. -/
theorem frame (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (pl : PoolLaws L) (law : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
 (hw : ∀ p q r, Free (law p q r))
 (a : TX2_240.Args) (s : SdkState) (env : Env) (o : Obs (Except ProgramError Unit × SdkState))
 (h : TX2_240.Ref L D (TCK.weaken V law) a s env o) :
 (∀ c b, Event.write c b ∉ o.events) ∧
 (∀ r s', o.exit = .ret (r,s') → ∀ i, (s'.cells i).payload=(s.cells i).payload) := by
 refine ⟨reference_free L D (TCK.weaken V law) pl hw a s env o h,?_⟩
 intro r s' ret
 rcases o with ⟨ex,events⟩
 simp only at ret
 subst ex
 exact NMV_G2.reference_frame L D (TCK.weaken V law) a s s' env r events h

#print axioms reference_free
#print axioms frame
end NMV_G2Reference
