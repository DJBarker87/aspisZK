import SInt2_S6SdkSourceCutReuseV1
set_option autoImplicit false
noncomputable section
namespace AspisS6SdkSelectedSemanticCut
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1.S2W_NativeConsolidation
open AspisS6CurrentFirstInstallation

/-- The original cut relation does not constrain an arbitrary f.semantic.
Choose the semantic argument actually selected by this accepted source call;
all other fields of the full published FirstCut are definitionally unchanged.
No additional source read/child-success/semantic-equality premise is added. -/
theorem selected_cut (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts accounts2 : Slice AdapterRw.Cuts.Account) (data : Slice U8)
    (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned (install ops vops)
      program accounts data = ok (.Ok saved))
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (install ops vops) accounts accounts2 saved f s) :
    ∃ semantic,
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement = ok semantic ∧
      SourceCuts (install ops vops) accounts accounts2 saved {f with semantic := semantic} s ∧
      f.split = AspisR1CurrentCaller.compact.SPLIT := by
  obtain ⟨semantic,selected,called,split⟩ :=
    AspisS6SdkSourceCutReuse.same_inputs ops vops program accounts accounts2 data saved accepted f s cuts
  exact ⟨semantic,selected,{cuts with first := called},split⟩

#print axioms selected_cut
end AspisS6SdkSelectedSemanticCut
end
