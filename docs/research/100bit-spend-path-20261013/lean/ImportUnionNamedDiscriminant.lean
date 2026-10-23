import Aeneas

/-! Aeneas discriminant readers with enum-qualified instance names for import unions.
The pinned generator supplies both commands; only its anonymous instance name
is changed. Scalar types, explicit tags, generic binders and reader bodies are
preserved. This adapter must be rebuilt when the Aeneas generator is repinned. -/
open Lean Elab Term Meta
open Lean.Parser.Term Lean.Parser.Command

namespace ImportUnionNamedDiscriminant

syntax (name := namedDiscriminant) "import_union_discriminant" ident ("["num,*"]")? : attr

initialize namedDiscriminantAttribute : AttributeImpl ← do
  let attrImpl : AttributeImpl := {
    «name» := `namedDiscriminant,
    descr := "Emit the Aeneas reader with an enum-qualified instance name",
    add := fun declName stx _ => do
      let (ty, values) ← match stx with
        | `(attr| import_union_discriminant $ty) =>
          pure (← Aeneas.Discriminant.elabTypeToken ty, none)
        | `(attr| import_union_discriminant $ty [$xs,*]) =>
          pure (← Aeneas.Discriminant.elabTypeToken ty,
            some ((xs.getElems.toList.map Syntax.isNatLit?).map Option.get!))
        | _ => throwUnsupportedSyntax
      liftCommandElabM do
        let cmds ← Lean.Elab.Command.liftTermElabM
          (Aeneas.Discriminant.generateReadDiscriminantCmds declName ty values)
        Lean.Elab.Command.elabCommand cmds[0]!
        let instName := mkIdent (declName ++ `instDiscriminant)
        let id ← `(Parser.Command.declId| $instName:ident)
        let inst := cmds[1]!.rewriteBottomUp fun node => Id.run do
          if node.isOfKind ``Lean.Parser.Command.instance then
            return node.setArg 3 (mkNullNode #[id.raw])
          return node
        if inst == cmds[1]! then
          throwError "Pinned Aeneas generator no longer emits an instance command"
        Lean.Elab.Command.elabCommand inst
  }
  registerBuiltinAttribute attrImpl
  pure attrImpl

end ImportUnionNamedDiscriminant
