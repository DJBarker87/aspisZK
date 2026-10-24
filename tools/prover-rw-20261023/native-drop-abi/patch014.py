"""Stop failed move lowering; retain independent printer fix and reject ABI gaps."""
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023')
p=H/'native-drop-abi/backend/base/src/PrePasses.ml'
s=(H/'native-drop/backend/base/src/PrePasses.ml').read_text()
addition='''(* ProverRwNativeDropABI: existing pair-valued builtin models have no
   validated nested-loan continuation. Never emit an apparently accepted
   nested swap/take through these models. Generic/hidden-region shapes reject. *)
let reject_unsupported_nested_builtin_abi (crate : crate) (f : fun_decl) : fun_decl =
  let mctx = NameMatcher.ctx_from_crate crate in
  let matches = NameMatcher.match_name mctx
    {map_vars_to_vars=true;
     match_with_trait_decl_refs=Config.match_patterns_with_trait_decl_refs} in
  let patterns = List.map NameMatcher.parse_pattern
    ["core::mem::swap"; "core::option::{core::option::Option<@T>}::take"] in
  let inspect (st : statement) =
    (match st.kind with
     | Call ({func=FnOpRegular {kind=FunId (FRegular id); generics}; _}, _) ->
       (match FunDeclId.Map.find_opt id crate.fun_decls with
        | Some d when List.exists (fun pat -> matches pat d.item_meta.name) patterns ->
          let unsupported=ref false in
          let visitor=object
            inherit [_] iter_ty as super
            method! visit_ty env ty =
              (match ty with
               | TRef _ | TVar _ -> unsupported:=true
               | TAdt {generics;_} when generics.regions<>[] -> unsupported:=true
               | _ -> ()); super#visit_ty env ty
          end in
          List.iter (visitor#visit_ty ()) generics.types;
          if !unsupported then [%craise] st.span
            "ProverRwNativeDropABI: nested swap/take requires validated full loan ABI"
        | _ -> ())
     | _ -> ()); [st] in
  match f.body with
  | StructuredBody body ->
      {f with body=StructuredBody {body with body=map_statement inspect body.body}}
  | _ -> f

'''
needle='let apply_passes (crate : crate) : crate ='
assert s.count(needle)==1
s=s.replace(needle,addition+needle).replace('("lower_precise_local_drops", lower_precise_local_drops);','("lower_precise_local_drops", lower_precise_local_drops);\n      ("reject_unsupported_nested_builtin_abi", reject_unsupported_nested_builtin_abi);')
p.write_text(s)
