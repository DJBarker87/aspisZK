import NDO_JFv_TX2_GatherActive
import JFv_TX2_TerminalMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_GatherLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeGeometryBody
abbrev State := core.slice.iter.Iter U32 × alloc.vec.Vec U32 × alloc.vec.Vec U32

def Inv (s : State) : Prop := s.1.slice=JFv_TX2_GatherShape.selected ∧ s.1.i≤12 ∧
  s.2.1.val=JFv_TX2_GatherShape.zs s.1.i ∧ s.2.2.val=JFv_TX2_GatherShape.flat s.1.i

def Meaning (g : verifier.QueryGeometry) : Prop :=
  g.start=10#usize ∧ g.line_z.val=JFv_TX2_GatherShape.zs 12 ∧
  ∃ inverse : alloc.vec.Vec U32,
    inverse.val.length=60 ∧
    (∀ j, j<60 → S7JoinBasisMachine.decode (Port4C_BatchInverse.cell inverse.val j)=
      (S7JoinBasisMachine.decode (Port4C_BatchInverse.cell (JFv_TX2_GatherShape.flat 12) j))⁻¹) ∧
    g.inverses.val=(List.range 12).map (Port4C_CollectLoop.record inverse)

def Post (out : core.result.Result verifier.QueryGeometry verifier.Error) : Prop :=
  ∃ g, out=.Ok g ∧ Meaning g

theorem source {C : Type} (err : C) (seed : Ops C) :
    ∃ out : verifier.QueryGeometry,
      verifier.QueryGeometry.for_range_loop0 (JFv_TX2_GeometryOps.install err seed)
        ⟨JFv_TX2_GatherShape.selected,0⟩ 10#usize (alloc.vec.Vec.new U32) (alloc.vec.Vec.new U32)=ok (.Ok out) ∧
      Meaning out := by
  have spec : verifier.QueryGeometry.for_range_loop0 (JFv_TX2_GeometryOps.install err seed)
      ⟨JFv_TX2_GatherShape.selected,0⟩ 10#usize (alloc.vec.Vec.new U32) (alloc.vec.Vec.new U32)
      ⦃ out => Post out ⦄ := by
    unfold verifier.QueryGeometry.for_range_loop0
    refine loop.spec_decr_nat (fun s : State => 12-s.1.i) Inv Post
      (fun (it,zs,flat) => verifier.QueryGeometry.for_range_loop0.body
        (JFv_TX2_GeometryOps.install err seed) 10#usize it zs flat)
      (⟨JFv_TX2_GatherShape.selected,0⟩,alloc.vec.Vec.new U32,alloc.vec.Vec.new U32) ?_ ?_
    · rintro ⟨it,zs,flat⟩ ⟨slice,bound,hzs,hflat⟩
      dsimp only at slice bound hzs hflat ⊢
      by_cases active : it.i<12
      · obtain ⟨zs1,flat1,run,zval,fval⟩ := JFv_TX2_GatherActive.source err seed it zs flat slice active hzs hflat
        rw [run,WP.spec_ok]
        refine ⟨⟨slice,by change it.i+1≤12;omega,zval,fval⟩,?_⟩
        change 12-(it.i+1)<12-it.i
        omega
      · have done : it.i=12 := by omega
        have ending : it.i=it.slice.val.length := by rw [slice];simp [JFv_TX2_GatherShape.selected,done]
        have zlen : zs.val.length=12 := by rw [hzs,(JFv_TX2_GatherShape.lengths _).1,done]
        have flen : flat.val.length=60 := by rw [hflat,(JFv_TX2_GatherShape.lengths _).2,done]
        obtain ⟨out,inverse,run,start,line,size,values,groups⟩ := JFv_TX2_TerminalMeaning.source err seed 10#usize it zs flat ending
          (by omega) (by omega) (by omega) (by rw [hflat];exact JFv_TX2_GatherShape.nonzero _)
        rw [run,WP.spec_ok]
        refine ⟨out,rfl,start,by rw [line,hzs,done],inverse,by omega,?_,?_⟩
        · intro j hj
          simpa only [hflat,done] using values j (by omega)
        · simpa only [zlen] using groups
    · exact ⟨rfl,by change 0≤12;omega,rfl,rfl⟩
  obtain ⟨result,run,out,he,meaning⟩ := WP.spec_imp_exists spec
  subst result
  exact ⟨out,run,meaning⟩
#print axioms source
end AspisR1.JFv_TX2_GatherLoop
end
