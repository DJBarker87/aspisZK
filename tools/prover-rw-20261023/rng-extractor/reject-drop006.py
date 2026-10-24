"""Conservative whole-crate rejection before passes/emission; no Drop erasure.
Does not implement destructor or escaping-reference semantics. Candidate only.
"""
from pathlib import Path
D=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor')
p=D/'base/src/Main.ml';s=p.read_text();needle='      (* Apply the pre-passes *)\n'
assert s.count(needle)==1
s=s.replace(needle,'''      (* ProverRwRngExtractor006: the inherited Drop path does not call
         drop_glue. Reject before any passes or emission, regardless of the
         drop_as_no_op flag. Escaping references also remain unsupported. *)
      let unsupported = ref [] in
      let drop_guard = object
        inherit [_] iter_statement as super
        method! visit_statement env st =
          (match st.kind with
          | Drop _ -> unsupported := "structured Drop requires destructor semantics" :: !unsupported
          | _ -> ());
          super#visit_statement env st
      end in
      let escape_guard = object
        inherit [_] iter_ty as super
        method! visit_ty env ty =
          (match ty with
          | TRef _ -> unsupported := "escaping reference output requires loan validation" :: !unsupported
          | _ -> ());
          super#visit_ty env ty
      end in
      FunDeclId.Map.iter
        (fun _ (f : fun_decl) ->
          escape_guard#visit_ty () f.signature.output;
          match f.body with
          | StructuredBody body -> drop_guard#visit_block () body.body
          | _ -> ()) m.fun_decls;
      if !unsupported <> [] then
        failwith ("ProverRwRngExtractor006: fail-closed preflight: " ^
          String.concat "; " (List.sort_uniq String.compare !unsupported));

'''+needle)
p.write_text(s)
