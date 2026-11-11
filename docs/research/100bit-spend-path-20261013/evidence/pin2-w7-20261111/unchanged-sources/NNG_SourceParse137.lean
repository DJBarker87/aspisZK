import NNG_SourcePublic137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceParse137
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport NMT_CallTree NNG_Context137 NNG_Observed136
open NNG_SourceStep136 NNG_DLawStep136

theorem source (a : NNG_Data137.Args) (obs : RSL.Observer) (env : RSL.Env)
    (domain : RSL.TX1_137.Domain NNG_Data137.VL a) :
    RSL.TX1_137.Ref LIB_VLib.library a env
      (observation (NNG_Output137.decode a env) (NNG_Events137.events env)
        (NNG_Tree137.tree (calls env) (input a obs env))) := by
  let head := invoke "TX1:138/parse" (NNG_Data137.bytes a.bytes) (NMP_Install138.parse (NNG_Data137.bytes a.bytes))
  let k : core.result.Result r1_wire.Prefix r1_wire.Error → Code (Output Unit) := fun reply=>
    match reply with
    | .Err e=>pure (.Err e)
    | .Ok p=>NNG_Tree137.mark0 (calls env) (input a obs env) p
  have split : NNG_Tree137.tree (calls env) (input a obs env) = NMT_CallTree.bind head k := by rfl
  rw [split]
  have headLaw : (LIB_VLib.library.parsePrefix.run a.bytes) env
      (observation (NNG_Parse137.decode a) (NNG_Events137.events env) head) := by
    change LIB_VParsePrefix.parsePrefix.run a.bytes env _
    rw [←NNG_Occurrences137.parse a env domain]
    exact call_actual _ NNG_Events137.events _ _ _ env
  unfold RSL.TX1_137.Ref RSL.RE.bind
  refine bind_sound head k (NNG_Parse137.decode a) (NNG_Output137.decode a env)
    (NNG_Events137.events env) env _ _ headLaw ?_
  intro reply returned
  have native := invoke_returned (NNG_Events137.events env) "TX1:138/parse" _ _ _ returned
  cases reply with
  | Err e=>
    change (⟨.ret (NNG_Output137.decode a env (.Err e)),[]⟩ : RSL.Obs _) = ⟨.ret (.error (toT12 e)),[]⟩
    rw [NNG_Head137.error]
  | Ok raw=>
    obtain ⟨p,parsed,same⟩ := NNG_Reached137.parse_eval a domain raw native
    subst raw
    simp only [NNG_Parse137.decode,parsed]
    dsimp only [k]
    unfold NNG_Tree137.mark0
    change (_ : RSL.Spec (Except LIB_VLib.library.WErr (RSL.Verified LIB_VLib.library))) env (observation _ _ (NMT_CallTree.bind (invoke "TX1:130/mark0" ((input a obs env).observer,0#u8) (.ok ())) (fun _=>_)))
    rw [NNG_Head137.mark _ env _ _ _ (NNG_Events137.silent env _ _ _ (by decide) (by decide) (by decide))]
    exact NNG_SourcePublic137.source a obs env domain p parsed
#print axioms source
end AspisR1.NNG_SourceParse137
