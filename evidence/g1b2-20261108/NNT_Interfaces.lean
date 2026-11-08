import TAS_Interfaces
set_option autoImplicit false
namespace RSL.NNT
open TAS
open TX2_241 (V2Lib Dom064)

def LawRefines (V0 : V2Lib) (R0 : Bytes → Bytes → Prop)
    (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)) : Prop :=
  ∀ (x : Bytes × Bytes × Bytes) (env : Env) (o : Obs (Except V0.VErr Unit)),
    Dom064 (lib V0 R0 w) x → V0.tx2auth x.1 x.2.1 x.2.2 env o → w x.1 x.2.1 x.2.2 env o

theorem lawRefines_canonical (V0 : V2Lib) : LawRefines V0 V0.Root0 V0.tx2auth :=
  fun _ _ _ _ h => h

theorem lawRefines_weak (V0 : V2Lib) : LawRefines V0 (fun _ _ => True) V0.tx2auth :=
  fun _ _ _ _ h => h

structure NMS_RootsL (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (I : Impl L V0 VL) where
  r242 : TX2_233.RowSpec_233 L D I.f233 → TX2_242.RowSpec_242 L D I.f242
  r241 : ∀ (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)),
    LawRefines V0 R0 w → TX2_242.RowSpec_242 L D I.f242 →
    TX2_241.RowSpec_241 L D (lib V0 R0 w) I.f241

structure NNC_G1aL (S : Sig) (L : PoolLib) (V0 : V2Lib) (VL : VLib)
    (I : Impl L V0 VL) where
  w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)
  lawRefines : LawRefines V0 (fun _ _ => True) w
  writeFree : ∀ p q r, WriteFree (w p q r)
  okHeader : ∀ pub pr ck env o, Dom064 (lib V0 (fun _ _ => True) w) (pub, pr, ck) →
    w pub pr ck env o → o.exit = .ret (.ok ()) → S.readerHeader env pub pr ck

example {L : PoolLib} {D : DeployedIds} {V0 : V2Lib} {VL : VLib} {I : Impl L V0 VL} :
    (TX2_233.RowSpec_233 L D I.f233 → TX2_242.RowSpec_242 L D I.f242) =
    (TX2_233.RowSpec_233 L D I.f233 → TX2_242.RowSpec_242 L D I.f242) := rfl
example {S : Sig} {L : PoolLib} {V0 : V2Lib} {VL : VLib} {I : Impl L V0 VL}
    (g : NNC_G1aL S L V0 VL I) (old : NNC_G1a S L V0 VL I) (same : g.w = old.w) :
    (∀ p q r, WriteFree (g.w p q r)) = (∀ p q r, WriteFree (old.w p q r)) := by rw [same]
example {S : Sig} {L : PoolLib} {V0 : V2Lib} {VL : VLib} {I : Impl L V0 VL}
    (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)) :
    (∀ pub pr ck env o, Dom064 (lib V0 (fun _ _ => True) w) (pub,pr,ck) →
      w pub pr ck env o → o.exit = .ret (.ok ()) → S.readerHeader env pub pr ck) =
    (∀ pub pr ck env o, Dom064 (lib V0 (fun _ _ => True) w) (pub,pr,ck) →
      w pub pr ck env o → o.exit = .ret (.ok ()) → S.readerHeader env pub pr ck) := rfl
#print axioms lawRefines_canonical
#print axioms lawRefines_weak
end RSL.NNT
