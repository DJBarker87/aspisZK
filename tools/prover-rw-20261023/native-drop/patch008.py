"""Isolated, unaccepted precise-local Drop lowering experiment; never installs."""
from pathlib import Path
D=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/native-drop/backend')
p=D/'base/src/PrePasses.ml';s=p.read_text()
needle='let apply_passes (crate : crate) : crate ='
assert s.count(needle)==1
addition='''(* ProverRwNativeDrop008: preserve and call actual regular precise glue.
   This candidate is unaccepted until complete loan/ABI regressions pass. *)
let lower_precise_local_drops (crate : crate) (f : fun_decl) : fun_decl =
  match f.body with
  | StructuredBody body ->
      let added = ref [] in
      let _, gen = LocalId.mk_stateful_generator_starting_at_id
        (LocalId.of_int (List.length body.locals.locals)) in
      let fresh ty =
        let id = gen () in
        added := { index = id; local_ty = ty; name = None;
                   span = body.span } :: !added;
        { kind = PlaceLocal id; ty } in
      let lower (st : statement) =
        let mk kind = { st with kind; statement_id = StatementId.zero } in
        match st.kind with
        | Drop (({kind = PlaceLocal original; _} as place),
                ({kind = FunId (FRegular _); _} as func), Precise, unwind) ->
            let borrowed = fresh (TRef (RErased, place.ty, RMut)) in
            let result = fresh mk_unit_ty in
            let id p = match p.kind with PlaceLocal id -> id | _ -> assert false in
            [mk (Assign (borrowed, RvRef (place, BMut, Constant mk_unit_const)));
             mk (Call ({func = FnOpRegular func; args = [Move borrowed]; dest = result}, unwind));
             mk (StorageDead (id result)); mk (StorageDead (id borrowed));
             mk (StorageDead original)]
        | Drop _ -> [%craise] st.span "ProverRwNativeDrop008: unsupported Drop shape"
        | _ -> [st] in
      let rewritten = map_statement lower body.body in
      {f with body = StructuredBody {body with body = rewritten;
         locals = {body.locals with locals = body.locals.locals @ List.rev !added}}}
  | _ -> f

(* Direct regular glue is a standalone function after marker-trait erasure.
   Retain its exact identity, body and signature; only detach item ownership. *)
let retain_called_drop_glue (crate : crate) : crate =
  let called = ref FunDeclId.Set.empty in
  let visitor = object
    inherit [_] iter_statement as super
    method! visit_statement env st =
      (match st.kind with
       | Drop (_, {kind = FunId (FRegular id); _}, Precise, _) ->
           called := FunDeclId.Set.add id !called
       | _ -> ()); super#visit_statement env st
  end in
  FunDeclId.Map.iter (fun _ (f : fun_decl) -> match f.body with
    | StructuredBody body -> visitor#visit_block () body.body | _ -> ()) crate.fun_decls;
  {crate with fun_decls = FunDeclId.Map.mapi (fun id (f : fun_decl) ->
    if FunDeclId.Set.mem id !called then {f with src = TopLevelItem} else f) crate.fun_decls}

'''
s=s.replace(needle,addition+needle).replace('let crate = update_array_default crate in','let crate = retain_called_drop_glue crate in\n  let crate = update_array_default crate in').replace('("decompose_global_accesses", decompose_global_accesses);','("decompose_global_accesses", decompose_global_accesses);\n      ("lower_precise_local_drops", lower_precise_local_drops);')
p.write_text(s)
p=D/'base/src/Main.ml';s=p.read_text();old='| Drop _ -> unsupported := "structured Drop requires destructor semantics" :: !unsupported'
new='''| Drop ({kind = PlaceLocal _; _}, {kind = Types.FunId (Types.FRegular id); _}, Precise, _)
              when not !Config.drop_as_no_op ->
              (match FunDeclId.Map.find_opt id m.fun_decls with
               | Some {body = StructuredBody _; _} -> ()
               | _ -> unsupported := "Drop glue requires a concrete structured body" :: !unsupported)
          | Drop _ -> unsupported := "unsupported Drop shape" :: !unsupported'''
assert s.count(old)==1;s=s.replace(old,new).replace('ProverRwRngExtractor006: fail-closed','ProverRwNativeDrop008: fail-closed');p.write_text(s)
