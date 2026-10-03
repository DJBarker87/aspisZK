open Aeneas
open Aeneas.LlbcOfJson
open Aeneas.LlbcAst

let bool b = if b then "MATCH" else "NO_MATCH"

let () =
  if Array.length Sys.argv <> 2 then failwith "usage: matcher_probe FILE.llbc";
  let crate =
    match crate_of_json_file Sys.argv.(1) with
    | Ok crate -> crate
    | Error error -> failwith error
  in
  let target =
    List.find (fun (d : fun_decl) -> d.def_id = FunDeclId.of_int 1)
      (FunDeclId.Map.values crate.fun_decls)
  in
  let ctx = Charon.NameMatcher.ctx_from_crate crate in
  let actual_name = target.item_meta.name in
  let actual_name_string =
    LlbcAstUtils.name_with_crate_to_pattern_string
      (Some target.item_meta.span) crate actual_name
  in
  let config : Charon.NameMatcher.match_config =
    {
      map_vars_to_vars = true;
      match_with_trait_decl_refs = Config.match_patterns_with_trait_decl_refs;
    }
  in
  let pattern_strings =
    [
      ("old", "core::slice::{[@T]}::len");
      ("added", "core::slice::{[@T]}::len<@T>");
      ("impl-var-leaf-u8", "core::slice::{[@T]}::len<u8>");
      ("impl-u8-leaf-var", "core::slice::{[u8]}::len<@T>");
      ("impl-var-leaf-other-var", "core::slice::{[@T]}::len<@U>");
      ("impl-var-leaf-wildcard", "core::slice::{[@T]}::len<@>");
      ("concrete-u8", "core::slice::{[u8]}::len<u8>");
    ]
  in
  Printf.printf "target Fun1 name pattern: %s\n" actual_name_string;
  let patterns =
    List.map (fun (label, text) -> (label, text, Charon.NameMatcher.parse_pattern text)) pattern_strings
  in
  List.iter
    (fun (label, _, pattern) ->
      Printf.printf "direct match_name_with_generics %s: %s\n" label
        (bool
           (Charon.NameMatcher.match_name_with_generics ctx config pattern
              actual_name TypesUtils.empty_generic_args));
      let map = ExtractBuiltin.NameMatcherMap.of_list [ (pattern, label) ] in
      Printf.printf "NameMatcherMap.find_opt %s: %s\n" label
        (match ExtractBuiltin.NameMatcherMap.find_opt ctx actual_name map with
        | Some _ -> "MATCH"
        | None -> "NO_MATCH");
      Printf.printf "NameMatcherMap.find_with_generics_opt(empty args) %s: %s\n"
        label
        (match
           ExtractBuiltin.NameMatcherMap.find_with_generics_opt ctx actual_name
             TypesUtils.empty_generic_args map
         with
        | Some _ -> "MATCH"
        | None -> "NO_MATCH"))
    patterns;
  let builtin = ExtractBuiltin.builtin_funs_map () in
  Printf.printf "candidate actual builtin_funs_map.find_opt Fun1: %s\n"
    (match ExtractBuiltin.NameMatcherMap.find_opt ctx actual_name builtin with
    | Some info -> Printf.sprintf "MATCH (%s)" info.extract_name
    | None -> "NO_MATCH");
  Printf.printf "candidate actual builtin_funs_map.find_with_generics_opt Fun1: %s\n"
    (match
       ExtractBuiltin.NameMatcherMap.find_with_generics_opt ctx actual_name
         TypesUtils.empty_generic_args builtin
     with
    | Some info -> Printf.sprintf "MATCH (%s)" info.extract_name
    | None -> "NO_MATCH")
