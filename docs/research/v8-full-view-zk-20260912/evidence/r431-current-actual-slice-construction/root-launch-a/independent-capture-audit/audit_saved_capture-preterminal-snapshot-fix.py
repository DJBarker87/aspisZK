#!/usr/bin/env python3
"""Offline audit of the saved R431 capture; never launches a process."""
from __future__ import annotations
import hashlib, json, re
from pathlib import Path

HERE = Path(__file__).resolve().parent.parent
OUT = Path(__file__).resolve().parent
SAVED = HERE / "saved-output"

def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()

def read(p: Path):
    return json.loads(p.read_text())

def remove_dest(argv):
    out=[]; i=0
    while i<len(argv):
        if argv[i] == "--dest-file":
            assert i+1<len(argv); i+=2
        else:
            out.append(argv[i]); i+=1
    return out

def remove_selected_includes(argv, selectors):
    out=[]; removed=[]; i=0
    while i<len(argv):
        if argv[i] == "--include" and i+1<len(argv) and argv[i+1] in selectors:
            removed.append(argv[i+1]); i+=2
        else:
            out.append(argv[i]); i+=1
    return out,removed

def stmt_name(s):
    k=s.get("kind")
    return next(iter(k)) if isinstance(k,dict) else k

def call_summary(fid, body):
    calls=[]
    def walk(x,path=""):
        if isinstance(x,dict):
            k=x.get("kind")
            if isinstance(k,dict) and "Call" in k:
                c=k["Call"]["call"]
                regular=c.get("func",{}).get("Regular",{})
                fkind=regular.get("kind",{}).get("Fun",{})
                target=fkind.get("Regular") if isinstance(fkind,dict) else None
                uw=k["Call"].get("on_unwind")
                cleanup=[]
                for q in (uw or {}).get("statements",[]): cleanup.append(stmt_name(q))
                calls.append({"function":fid,"path":path,"target_fun_id":target,
                              "args":c.get("args"),"dest":c.get("dest"),
                              "unwind_statements":cleanup,
                              "unwind_ids":[q.get("id") for q in (uw or {}).get("statements",[])]})
            for key,val in x.items(): walk(val,path+"/"+str(key))
        elif isinstance(x,list):
            for i,val in enumerate(x): walk(val,path+"/"+str(i))
    walk(body)
    return calls

def name_text(parts):
    out=[]
    for part in parts:
        if "Ident" in part: out.append(part["Ident"][0])
        elif "Impl" in part: out.append("{impl}")
        elif "Instantiated" in part: continue
    return "::".join(out)

command_obj=read(SAVED/"extract-command.json")
base_obj=read(HERE/"r429-command.snapshot.json")
change=read(HERE/"changed-scope-receipt.json")
launch=read(HERE/"launch-status.json")
collection=read(HERE/"collection-status.json")
result=read(SAVED/"result.json")
before=read(SAVED/"host-reservation-before.json")
after=read(SAVED/"host-reservation-after.json")
cgroup=read(SAVED/"runner-status.json")["effective_cgroup"]
llbc_path=SAVED/"R431ActualSliceConstruction.llbc"
llbc_sha=sha(llbc_path)
raw=json.loads(llbc_path.read_text())
tr=raw["translated"]

expected_additions=["core::slice::_::iter","core::slice::iter::_::new"]
base_argv=remove_dest(base_obj["command"])
current_without_added_includes, removed=remove_selected_includes(command_obj["command"], expected_additions)
assert sorted(removed)==sorted(expected_additions), removed
assert remove_dest(current_without_added_includes)==base_argv, "command differs beyond output path and the two reviewed include pairs"
assert sha(HERE/"r429-command.snapshot.json")==change["predecessor_command_sha256"]
assert sha(llbc_path)=="df9180ee7c9959a7840d6edac0b756f007ef33ed0bd88bb36faf57a3e18f2358"
assert result["llbc_sha256"]==llbc_sha
assert result["charon_exit_status"]==0 and result["has_errors"] is False
assert launch["ssh_exit_status"]==0 and collection["exit_status"]==0
assert launch["launch_revision"]==result["capture_revision"]==change["launch_revision"]
assert launch["remote_script_sha256"]==change["remote_script_sha256"]
assert command_obj["base_extract_command_sha256"]==result["base_extract_command_sha256"]
assert command_obj["baseline_sha256"]==result["baseline_sha256_before_after"][0]==result["baseline_sha256_before_after"][1]
assert before["baseline_sha_before"]==after["baseline_sha_after"]==command_obj["baseline_sha256"]
assert result["source_hashes_before_after"]["before"]==result["source_hashes_before_after"]["after"]
assert result["source_hashes_before_after"]["before"]==command_obj["source_hashes"]
assert before["source_hashes_before"]==after["source_hashes_after"]==command_obj["source_hashes"]
assert before["stdlib_hashes_before"]==after["stdlib_hashes_after"]
assert before["driver_sha256"]==before["original_driver_sha256"]==result["original_driver_sha256"]
assert before["wrapper_sha256"]=="b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c"
assert before["caps"]=={"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":"0","TasksMax":128}
assert cgroup["memory.high"]=="5368709120" and cgroup["memory.max"]=="7516192768"
assert cgroup["memory.swap.max"]=="0" and cgroup["pids.max"]=="128"
assert cgroup["memory.swap.current"]==cgroup["memory.swap.peak"]=="0"
assert all(re.search(r"(?:^|\n)"+key+r" 0(?:\n|$)",cgroup["memory.events"]) for key in ("oom","oom_kill","oom_group_kill"))
assert result["formal_axioms"]=="N/A; diagnostic LLBC only"

# Exact declaration and layout census.
selected_funcs={i:tr["fun_decls"][i] for i in (29,43,86)}
selected_types={i:tr["type_decls"][i] for i in (2,42,58,69)}
selected_globals={31:tr["global_decls"][31]}
assert all(selected_funcs[i] is not None for i in selected_funcs)
assert name_text(selected_funcs[29]["item_meta"]["name"])=="aspis_v8_performance_host::freeze::{impl}::call"
assert name_text(selected_funcs[43]["item_meta"]["name"]).startswith("core::slice::{impl}::iter")
assert name_text(selected_funcs[86]["item_meta"]["name"]).startswith("core::slice::iter::{impl}::new")
assert selected_funcs[29]["item_meta"]["opacity"]=="Transparent"
assert selected_funcs[43]["item_meta"]["opacity"]==selected_funcs[86]["item_meta"]["opacity"]=="Transparent"
assert all("Structured" in selected_funcs[i]["body"] for i in selected_funcs)
assert selected_types[42]["item_meta"]["opacity"]=="Transparent"
assert selected_types[58]["kind"]=="Opaque" and selected_types[69]["kind"]=="Opaque"
assert selected_types[2]["item_meta"]["name"][-1]["Ident"][0]=="QM31"
assert selected_globals[31]["item_meta"]["opacity"]=="Transparent"

# Required call chain and unwind inventory.
calls={i:call_summary(i,f["body"]["Structured"]) for i,f in selected_funcs.items()}
assert any(c["target_fun_id"]==43 for c in calls[29])
assert any(c["target_fun_id"]==70 for c in calls[29])
assert any(c["target_fun_id"]==86 for c in calls[43])
assert not calls[86]

# Capture exact rows plus every hash-consed value used by those rows, resolving
# Deduplicated references against their retained HashConsedValue occurrence.
ded=set(); used_hashcons=set()
def scan(x):
    if isinstance(x,dict):
        if "Deduplicated" in x and isinstance(x["Deduplicated"],int): ded.add(x["Deduplicated"])
        if "HashConsedValue" in x and isinstance(x["HashConsedValue"],list): used_hashcons.add(x["HashConsedValue"][0])
        for v in x.values(): scan(v)
    elif isinstance(x,list):
        for v in x: scan(v)
for row in list(selected_funcs.values())+list(selected_types.values())+list(selected_globals.values()): scan(row)
wrappers={}
def all_hcons(x,path=""):
    if isinstance(x,dict):
        if "HashConsedValue" in x:
            i,v=x["HashConsedValue"]
            wrappers.setdefault(i,[]).append({"path":path,"value":v})
        for k,v in x.items(): all_hcons(v,path+"/"+str(k))
    elif isinstance(x,list):
        for i,v in enumerate(x): all_hcons(v,path+"/"+str(i))
all_hcons(tr)
assert ded <= set(wrappers), sorted(ded-set(wrappers))

f86=selected_funcs[86]["body"]["Structured"]["body"]["statements"]
assert len(f86)==28
assert list(f86[18]["kind"])[0]=="Switch" and "If" in f86[18]["kind"]["Switch"]
branches=f86[18]["kind"]["Switch"]["If"]
true_stmts=branches[1]["statements"]; false_stmts=branches[2]["statements"]
assert len(true_stmts)==1 and len(false_stmts)==7
assert true_stmts[0]["kind"]["Assign"][0]["kind"]=={"Local":5}
assert true_stmts[0]["kind"]["Assign"][1]["UnaryOp"][0]["Cast"]["Transmute"]==[{"Deduplicated":887},{"Deduplicated":4178}]
offset_stmt=next(s for s in false_stmts if "Assign" in s.get("kind",{}) and s["kind"]["Assign"][1].get("BinaryOp",[None])[0]=="Offset")
off_lhs,off_rhs=offset_stmt["kind"]["Assign"]
assert off_lhs["kind"]=={"Local":6}
assert off_rhs["BinaryOp"][1]["Copy"]["kind"]=={"Local":7} and off_rhs["BinaryOp"][2]["Copy"]["kind"]=={"Local":2}
aggregate=f86[21]["kind"]["Assign"][1]["Aggregate"]
assert aggregate[0]["Adt"][0]["id"]=={"Adt":42} and len(aggregate[1])==3
assert aggregate[1][0]["Copy"]["kind"]=={"Local":3}
assert aggregate[1][1]["Copy"]["kind"]=={"Local":5}
assert aggregate[1][2]["Move"]["kind"]=={"Local":11}
assert any("Assign" in s.get("kind",{}) and s["kind"]["Assign"][1].get("RawPtr") is not None for s in f86)
assert any("Assign" in s.get("kind",{}) and s["kind"]["Assign"][1].get("Ref") is not None for s in selected_funcs[29]["body"]["Structured"]["body"]["statements"])
assert any("Assign" in s.get("kind",{}) and "UnaryOp" in s["kind"]["Assign"][1] and s["kind"]["Assign"][1]["UnaryOp"][0].get("Cast",{}).get("RawPtr") is not None for s in false_stmts)

# Emit complete, unchanged declaration rows and precise operation audit.
rows={"llbc_sha256":llbc_sha,"fun_decls":{str(i):f for i,f in selected_funcs.items()},
      "type_decls":{str(i):t for i,t in selected_types.items()},
      "global_decls":{str(i):g for i,g in selected_globals.items()}}
(OUT/"selected-rows.json").write_text(json.dumps(rows,indent=2,sort_keys=True)+"\n")

summary={
  "audit": "saved-artifact-only; no extraction, build, Lean, or source edit",
  "capture": {"path": str(llbc_path),"sha256":llbc_sha,"has_errors":raw["has_errors"],
              "charon_version":raw["charon_version"],"crate_name":tr["crate_name"],"declaration_counts":{k:sum(x is not None for x in tr[k]) for k in ("type_decls","fun_decls","global_decls","trait_decls","trait_impls")},
              "result_sha256":sha(SAVED/"result.json"),"launch_status_sha256":sha(HERE/"launch-status.json"),
              "collection_status_sha256":sha(HERE/"collection-status.json"),
              "launch_revision":launch["launch_revision"],"source_commit":result["source_commit"],
              "formal_axioms":result["formal_axioms"]},
  "command_delta": {"predecessor_command_snapshot_sha256":sha(HERE/"r429-command.snapshot.json"),
                    "recorded_predecessor_command_sha256":change["predecessor_command_sha256"],
                    "predecessor_llbc_sha256":change["predecessor_llbc_sha256"],
                    "added_include_paths_in_order":expected_additions,
                    "destination":command_obj["command"][command_obj["command"].index("--dest-file")+1],
                    "only_differences":change["only_command_changes"],"comparison":"PASS"},
  "source_and_tool": {"frozen_source_hashes_before_after_equal":True,
                       "baseline_before_after_equal":True,
                       "nightly_stdlib_hashes_before_after_equal":True,
                       "rustc":result["rustc_version_verbose"],"charon_toolchain":result["charon_toolchain"],
                       "wrapper_sha256":before["wrapper_sha256"],"driver_sha256":before["driver_sha256"],
                       "rustflags_sha256":before["rustflags_sha256"],"rustflags":before["rustflags"]},
  "metrics": {"charon_exit_status":result["charon_exit_status"],"GNU_elapsed":result["wall_time"],
               "GNU_max_rss_kib":result["peak_rss_kib"],"GNU_swap_count":result["swap_count"],
               "GNU_time_exit_status":result["gnu_time_exit_status"],"cgroup":cgroup,
               "runner_status_cgroup_peak_bytes":int(cgroup["memory.peak"]),
               "runner_status_cgroup_peak_kib":int(cgroup["memory.peak"])//1024,
               "host_reservation_after_cgroup_peak_bytes":int(after["effective_cgroup_after"]["memory.peak"]),
               "host_reservation_after_cgroup_peak_kib":int(after["effective_cgroup_after"]["memory.peak"])//1024,
               "measurement_note":"GNU per-process max RSS and cgroup peak snapshots are recorded from their respective receipts; they differ and are reported separately, with no equality assumption"},
  "selected_declarations": {"functions":{str(i):{"display_name":name_text(f["item_meta"]["name"]),
       "is_local":f["item_meta"]["is_local"],"opacity":f["item_meta"]["opacity"],
       "signature":f["signature"],"source":f["src"],"structured_top_level_statements":len(f["body"]["Structured"]["body"]["statements"])}
       for i,f in selected_funcs.items()},
       "type42_fields":[{"name":q["name"],"type":q["ty"]} for q in selected_types[42]["kind"]["Struct"]],
       "type58":{"display_name":name_text(selected_types[58]["item_meta"]["name"]),"kind":selected_types[58]["kind"],"layout":selected_types[58]["layout"]},
       "type69":{"display_name":name_text(selected_types[69]["item_meta"]["name"]),"kind":selected_types[69]["kind"],"layout":selected_types[69]["layout"]},
       "QM31_type_id":2,"QM31_fields":[q["name"] for q in selected_types[2]["kind"]["Struct"]],
       "global31":{"display_name":name_text(selected_globals[31]["item_meta"]["name"]),"opacity":selected_globals[31]["item_meta"]["opacity"],"src":selected_globals[31]["src"]}},
  "calls_and_unwinds": calls,
  "fun86_control_and_ops": {"top_level_statement_count":len(f86),"switch_statement_id":f86[18]["id"],
       "switch_condition":branches[0],"if_true_arm_statement_ids":[s["id"] for s in true_stmts],
       "if_false_arm_statement_ids":[s["id"] for s in false_stmts],
       "if_true_arm":true_stmts,"if_false_arm":false_stmts,
       "offset_assignment":offset_stmt,"result_aggregate":f86[21],
       "selected_op_tags":sorted({next(iter(s["kind"]["Assign"][1])) for s in f86 if isinstance(s.get("kind"),dict) and "Assign" in s["kind"]})},
  "hashcons": {"deduplicated_id_count":len(ded),"all_deduplicated_ids_resolve_to_retained_hashcons_value":True,
       "ids":{str(i):{"occurrences":len(wrappers[i]),"first_path":wrappers[i][0]["path"],"value":wrappers[i][0]["value"]}
              for i in sorted(ded)}},
  "audit_result":"PASS for saved capture integrity/structure; no source-semantics, pointer-validity, or memory-model conclusion"
}
(OUT/"audit.json").write_text(json.dumps(summary,indent=2,sort_keys=True)+"\n")
print(json.dumps({"result":summary["audit_result"],"llbc_sha256":llbc_sha,"fun29_calls":[c["target_fun_id"] for c in calls[29]],
                  "fun43_calls":[c["target_fun_id"] for c in calls[43]],"GNU_rss_kib":result["peak_rss_kib"],
                  "runner_cgroup_peak_kib":summary["metrics"]["runner_status_cgroup_peak_kib"],"host_cgroup_peak_kib":summary["metrics"]["host_reservation_after_cgroup_peak_kib"],"metrics_note":summary["metrics"]["measurement_note"]},indent=2))
