import NNG_ProducerFull094
import NNG_ParsedTail094
import NNG_ParseOriginal094
import NNG_TotalParse094
import NNG_ReferenceMatch094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ScanTail094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136 NNG_Carriers094

theorem source (a : NNG_Input094.Args) (obs : RSL.Observer) (env : RSL.Env)
 (own : RSL.TX1_094.Domain LIB_Instances.VL a obs a.public_) (split : a.k=10)
 (ep : List RSL.Event) (parsed : LIB_Instances.VL.parseShape.run a.proof env ⟨.ret (.ok ()),ep⟩) :
 RSL.RE.seq (LIB_Instances.VL.canonicalScan.run a.proof)
  (NNG_ReferenceMatch094.original a) env
  (observation NNG_Producer094.port (NNG_Events094.events env)
   (NNG_PrepareTree094.f_r1 (NNG_InstalledCalls094.calls env) (NNG_Input094.input a obs env))) := by
 have originalWidth := NNG_TotalParse094.returned_width a.proof env ep parsed
 rw [←NNG_ReferenceMatch094.same a obs env own split originalWidth]
 let s := NNG_Input094.input a obs env
 let code := NNG_Tree094.NNG_call_2 (NNG_InstalledCalls094.calls env).c2 s.proof
 let tail : core.result.Result Unit verifier.Error → Code NNG_Context094.Output := fun r=>do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue _=>NNG_PrepareTree094.f_markParsed (NNG_InstalledCalls094.calls env) s
  | .Break residual=>monadLift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual)
 have width := NNG_TotalParse094.returned_width a.proof env ep parsed
 have proofSame : LIB_Carriers.bytes s.proof=a.proof := LIBC_Bytes.to_native a.proof (by rw [width];scalar_tac)
 have nativeWidth : s.proof.val.length=57607 := by
  have h := congrArg List.length proofSame
  rw [NMS_R2N_RSLScalars.bytes_length,width] at h
  exact h
 have head : LIB_Instances.VL.canonicalScan.run a.proof env
  (observation NNG_ScanCall094.port (NNG_Events094.events env) code) := by
  have graph := NNG_ScanCall094.graph env s.proof nativeWidth
  rw [proofSame] at graph
  unfold code NNG_Tree094.NNG_call_2
  rw [NNG_InvokeGraph094.observation,NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide)]
  exact graph
 change RSL.Spec.bind _ _ env (observation NNG_Producer094.port (NNG_Events094.events env) (NMT_CallTree.bind code tail))
 apply NNG_SourceStep136.bind_sound code tail NNG_ScanCall094.port
  NNG_Producer094.port (NNG_Events094.events env) env _ _ head
 intro r returned
 cases r with
 | Err e=>rfl
 | Ok u=>
  cases u
  have scanned := NNG_InvokeReturned094.silent env _ _ _ (core.result.Result.Ok ()) NNG_ScanCall094.port
   (LIB_Instances.VL.canonicalScan.run a.proof) head returned
   (NNG_Events094.silent env _ _ _ (by decide) (by decide) (by decide))
  have domain := NNG_TotalParse094.prepare_domain a env ep [] own.2.1 parsed scanned
  have publicSame : toT9 s.publicValue=a.public_ := fromT9_inverse _
  have arguments : NNG_PrepareTail094.args s=⟨a.public_,a.proof,LIB_Instances.VL.zeroE29⟩ := by
   unfold NNG_PrepareTail094.args
   rw [publicSame,proofSame]
  have nativeSplit : s.k.val=10 := by
   change (LIBC_Usize.raw a.k).val=10
   rw [split]
   exact LIBC_Usize.raw_val 10 (by scalar_tac)
  exact NNG_ParsedTail094.source env s rfl rfl nativeSplit
   (Eq.mp (congrArg (fun input=>RSL.TX1_087.Domain LIB_Instances.VL input none) arguments.symm) domain)
   (by rw [proofSame];exact width)
   (by rw [NNG_Input094.public_extent a obs env own];exact own.2.2)
#print axioms source
end AspisR1.NNG_ScanTail094
