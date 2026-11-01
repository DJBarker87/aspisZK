import PV_EVH_Entropy
import PV_EVH_SliceBind
import PV_EVH_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_EVH_EntropyStep
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- Every non-language callee is explicitly OPEN. This structure supplies
neither a complete native event trace nor any successful run witness. -/
structure Callees where
  op128_OPEN : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : Z), P ((zeroize.Zeroizing Z))
  op125_OPEN : ∀ {T : Type} {Z : Type} (coreconvertAsMutInst : core.convert.AsMut Z T)
      (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), P ((T × (T → zeroize.Zeroizing Z)))
  op126_OPEN : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), P ((Z × (Z → zeroize.Zeroizing Z)))
  op127_OPEN : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), P (Z)
  arrayIndex_OPEN : ∀ {T I Output : Type} {N : Usize} (inst : core.ops.index.Index (Slice T) I Output) (a : Array T N) (i : I), P (Output)
  sliceCopy_OPEN : ∀ {T : Type} (inst : core.marker.Copy T) (dst src : Slice T), P (Slice T)
  entropy_nonzero32_OPEN : ∀ (bytes : Array Std.U8 32#usize), P (Bool)

structure Compatible (c : Callees) : Prop where
  op128_fixed : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : Z), FinishedView (c.op128_OPEN ZeroizeInst arg0) (zeroize.Zeroizing.new ZeroizeInst arg0)
  op125_fixed : ∀ {T : Type} {Z : Type} (coreconvertAsMutInst : core.convert.AsMut Z T)
      (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), FinishedView (c.op125_OPEN coreconvertAsMutInst ZeroizeInst arg0) (zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut coreconvertAsMutInst ZeroizeInst arg0)
  op126_fixed : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), FinishedView (c.op126_OPEN ZeroizeInst arg0) (zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut ZeroizeInst arg0)
  op127_fixed : ∀ {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) (arg0 : (zeroize.Zeroizing Z)), FinishedView (c.op127_OPEN ZeroizeInst arg0) (zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref ZeroizeInst arg0)
  arrayIndex_fixed : ∀ {T I Output : Type} {N : Usize} (inst : core.ops.index.Index (Slice T) I Output) (a : Array T N) (i : I), FinishedView (c.arrayIndex_OPEN inst a i) (core.array.Array.index inst a i)
  sliceCopy_fixed : ∀ {T : Type} (inst : core.marker.Copy T) (dst src : Slice T), FinishedView (c.sliceCopy_OPEN inst dst src) (core.slice.Slice.copy_from_slice inst dst src)
  entropy_nonzero32_fixed : ∀ (bytes : Array Std.U8 32#usize), FinishedView (c.entropy_nonzero32_OPEN bytes) (aspis_prover.state_only_entropy.entropy_nonzero32 bytes)

open ControlFlow

def run
  (mask_nonce : Array Std.U8 32#usize) (limit : Std.Usize) (retry : Std.Usize) (entropyAnswers : PV_EVH_Entropy.EntropyAnswers) (c : Callees) : P (ControlFlow Std.Usize (core.result.Result
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
    aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError)) := do
  if retry < limit then
    let a := Array.repeat 64#usize 0#u8
    let bytes ← c.op128_OPEN (Array.Insts.ZeroizeZeroize 64#usize
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a
    let (s, as_mut_back) ← c.op125_OPEN
        (Array.Insts.CoreConvertAsMutSlice Std.U8 64#usize)
        (Array.Insts.ZeroizeZeroize 64#usize (zeroize.Zeroize.Blanket
        U8.Insts.ZeroizeDefaultIsZeroes)) bytes
    let (r, s1) ← PV_EVH_Prefix.ofM (PV_EVH_Entropy.draw entropyAnswers s)
    let cf ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let bytes1 := as_mut_back s1
      let a1 := Array.repeat 32#usize 0#u8
      let field_mask_entropy ← c.op128_OPEN (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a1
      let a2 := Array.repeat 32#usize 0#u8
      let leaf_salt_seed ← c.op128_OPEN (Array.Insts.ZeroizeZeroize 32#usize
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a2
      let (a3, deref_mut_back) ← c.op126_OPEN
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) field_mask_entropy
      let (s2, to_slice_mut_back) ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice_mut a3))
      let a4 ← c.op127_OPEN
          (Array.Insts.ZeroizeZeroize 64#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) bytes1
      let s3 ← c.arrayIndex_OPEN (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) a4
          { «end» := 32#usize }
      let s4 ← c.sliceCopy_OPEN core.marker.CopyU8 s2 s3
      let a5 := to_slice_mut_back s4
      let field_mask_entropy1 := deref_mut_back a5
      let (a6, deref_mut_back1) ← c.op126_OPEN
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) leaf_salt_seed
      let (s5, to_slice_mut_back1) ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Array.to_slice_mut a6))
      let s6 ← c.arrayIndex_OPEN (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)) a4
          { start := 32#usize }
      let s7 ← c.sliceCopy_OPEN core.marker.CopyU8 s5 s6
      let a7 := to_slice_mut_back1 s7
      let leaf_salt_seed1 := deref_mut_back1 a7
      let a8 ← c.op127_OPEN
          (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
          U8.Insts.ZeroizeDefaultIsZeroes)) field_mask_entropy1
      let b ← c.entropy_nonzero32_OPEN a8
      if b then
        let a9 ← c.op127_OPEN
            (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket
            U8.Insts.ZeroizeDefaultIsZeroes)) leaf_salt_seed1
        let b1 ← c.entropy_nonzero32_OPEN a9
        if b1 then
          pure (done (core.result.Result.Ok
            {
            mask_nonce,
            field_mask_entropy := field_mask_entropy1,
            leaf_salt_seed := leaf_salt_seed1
            }))
        else
          let retry1 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Std.Usize.wrapping_add retry 1#usize))
          pure (cont retry1)
      else
        let retry1 ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Std.Usize.wrapping_add retry 1#usize))
        pure (cont retry1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
          aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.Insts.CoreConvertFromError
          residual)
      pure (done r1)
  else
    pure (done (core.result.Result.Err
      aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.RepeatedZeroBlock))

theorem run_fixed
  (mask_nonce : Array Std.U8 32#usize) (limit : Std.Usize) (retry : Std.Usize) (entropyAnswers : PV_EVH_Entropy.EntropyAnswers) (c : Callees) (compatible : Compatible c) (entropy_same : ∀ n s, entropyAnswers n s = getrandom.fill s) :
    FinishedView (run mask_nonce limit retry entropyAnswers c) (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body mask_nonce limit retry) := by
  unfold run aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
  by_cases condition : retry < limit
  · simp only [condition,if_true]
    let a := Array.repeat 64#usize 0#u8
    try dsimp only
    try dsimp only
    apply PV_EVH_Prefix.bind_fixed
    ·
      exact compatible.op128_fixed _ _
    · intro bytes
      try dsimp only
      apply PV_EVH_Prefix.bind_fixed
      ·
        exact compatible.op125_fixed _ _ _
      · rintro ⟨s, as_mut_back⟩
        try dsimp only
        apply PV_EVH_Prefix.bind_fixed
        ·
          exact PV_EVH_Prefix.ofM_fixed _ _ (PV_EVH_Entropy.draw_fixed entropyAnswers entropy_same _) 
        · rintro ⟨r, s1⟩
          try dsimp only
          apply PV_EVH_Prefix.bind_fixed
          ·
            exact PV_EVH_Prefix.lift_fixed _
          · intro cf
            try dsimp only
            cases cf with
            | Continue unused0 =>
              let bytes1 := as_mut_back s1
              try dsimp only
              let a1 := Array.repeat 32#usize 0#u8
              try dsimp only
              try dsimp only
              apply PV_EVH_Prefix.bind_fixed
              ·
                exact compatible.op128_fixed _ _
              · intro field_mask_entropy
                let a2 := Array.repeat 32#usize 0#u8
                try dsimp only
                try dsimp only
                apply PV_EVH_Prefix.bind_fixed
                ·
                  exact compatible.op128_fixed _ _
                · intro leaf_salt_seed
                  try dsimp only
                  apply PV_EVH_Prefix.bind_fixed
                  ·
                    exact compatible.op126_fixed _ _
                  · rintro ⟨a3, deref_mut_back⟩
                    apply PV_EVH_SliceBind.pure_bind_fixed
                    let s2 := (Array.to_slice_mut a3).1
                    let to_slice_mut_back := (Array.to_slice_mut a3).2
                    try dsimp only
                    apply PV_EVH_Prefix.bind_fixed
                    ·
                      exact compatible.op127_fixed _ _
                    · intro a4
                      try dsimp only
                      apply PV_EVH_Prefix.bind_fixed
                      ·
                        exact compatible.arrayIndex_fixed _ _ _
                      · intro s3
                        try dsimp only
                        apply PV_EVH_Prefix.bind_fixed
                        ·
                          exact compatible.sliceCopy_fixed _ _ _
                        · intro s4
                          let a5 := to_slice_mut_back s4
                          try dsimp only
                          let field_mask_entropy1 := deref_mut_back a5
                          try dsimp only
                          try dsimp only
                          apply PV_EVH_Prefix.bind_fixed
                          ·
                            exact compatible.op126_fixed _ _
                          · rintro ⟨a6, deref_mut_back1⟩
                            apply PV_EVH_SliceBind.pure_bind_fixed
                            let s5 := (Array.to_slice_mut a6).1
                            let to_slice_mut_back1 := (Array.to_slice_mut a6).2
                            try dsimp only
                            apply PV_EVH_Prefix.bind_fixed
                            ·
                              exact compatible.arrayIndex_fixed _ _ _
                            · intro s6
                              try dsimp only
                              apply PV_EVH_Prefix.bind_fixed
                              ·
                                exact compatible.sliceCopy_fixed _ _ _
                              · intro s7
                                let a7 := to_slice_mut_back1 s7
                                try dsimp only
                                let leaf_salt_seed1 := deref_mut_back1 a7
                                try dsimp only
                                try dsimp only
                                apply PV_EVH_Prefix.bind_fixed
                                ·
                                  exact compatible.op127_fixed _ _
                                · intro a8
                                  try dsimp only
                                  apply PV_EVH_Prefix.bind_fixed
                                  ·
                                    exact compatible.entropy_nonzero32_fixed _
                                  · intro b
                                    by_cases condition : b
                                    · try dsimp only [a,bytes1,a1,a2,s2,to_slice_mut_back,a5,field_mask_entropy1,s5,to_slice_mut_back1,a7,leaf_salt_seed1] at condition
                                      simp only [condition,if_true]
                                      try dsimp only
                                      apply PV_EVH_Prefix.bind_fixed
                                      ·
                                        exact compatible.op127_fixed _ _
                                      · intro a9
                                        try dsimp only
                                        apply PV_EVH_Prefix.bind_fixed
                                        ·
                                          exact compatible.entropy_nonzero32_fixed _
                                        · intro b1
                                          by_cases condition : b1
                                          · try dsimp only [a,bytes1,a1,a2,s2,to_slice_mut_back,a5,field_mask_entropy1,s5,to_slice_mut_back1,a7,leaf_salt_seed1] at condition
                                            simp only [condition,if_true]
                                            exact PV_EVH_Prefix.lift_fixed _
                                          · try dsimp only [a,bytes1,a1,a2,s2,to_slice_mut_back,a5,field_mask_entropy1,s5,to_slice_mut_back1,a7,leaf_salt_seed1] at condition
                                            simp only [condition,Bool.false_eq_true,if_false]
                                            try dsimp only
                                            apply PV_EVH_Prefix.bind_fixed
                                            ·
                                              exact PV_EVH_Prefix.lift_fixed _
                                            · intro retry1
                                              exact PV_EVH_Prefix.lift_fixed _
                                    · try dsimp only [a,bytes1,a1,a2,s2,to_slice_mut_back,a5,field_mask_entropy1,s5,to_slice_mut_back1,a7,leaf_salt_seed1] at condition
                                      simp only [condition,Bool.false_eq_true,if_false]
                                      try dsimp only
                                      apply PV_EVH_Prefix.bind_fixed
                                      ·
                                        exact PV_EVH_Prefix.lift_fixed _
                                      · intro retry1
                                        exact PV_EVH_Prefix.lift_fixed _
            | Break residual =>
              try dsimp only
              apply PV_EVH_Prefix.bind_fixed
              ·
                exact PV_EVH_Prefix.lift_fixed _
              · intro r1
                exact PV_EVH_Prefix.lift_fixed _
  · simp only [condition,Bool.false_eq_true,if_false]
    exact PV_EVH_Prefix.lift_fixed _

#print axioms run_fixed
end PV_EVH_EntropyStep
