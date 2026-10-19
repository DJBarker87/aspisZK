#!/usr/bin/env python3
import copy, hashlib, json, pathlib, sys
attempt = pathlib.Path(__file__).resolve().parent
original = attempt.parent.parent / "attempt-f-row-helper/output/Terminal.llbc"
adapted = attempt / "Terminal-name-adapt.llbc"
expected_original = "da94ddf1971c135c593192457d508decd84003623bfe6ff0d232883fe3a90639"
expected_adapted = "58708e0d42a6d9c4e31dd102d2ec4d7de8abc07ccb8be9d9ecd3ffaf57875644"
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(original) == expected_original
assert sha(adapted) == expected_adapted
o = json.loads(original.read_bytes())
a = json.loads(adapted.read_bytes())
assert a["translated"]["fun_decls"][236]["def_id"] == 236
assert a["translated"]["fun_decls"][236]["item_meta"]["attr_info"]["rename"] == "M31_constructor"
assert o["translated"]["fun_decls"][236]["item_meta"]["attr_info"]["rename"] is None
b = copy.deepcopy(a)
b["translated"]["fun_decls"][236]["item_meta"]["attr_info"]["rename"] = None
assert b == o, "more than the authorized rename metadata differs"
assert a["translated"]["type_decls"][14] == o["translated"]["type_decls"][14]
assert a["translated"]["item_names"] == o["translated"]["item_names"]
assert a["translated"]["ordered_decls"] == o["translated"]["ordered_decls"]
print(json.dumps({"status":"pass","original_sha256":sha(original),"adapted_sha256":sha(adapted),"only_changed_json_path":"translated.fun_decls[236].item_meta.attr_info.rename","type14_unchanged":True,"item_names_unchanged":True,"ordered_decls_unchanged":True},indent=2))
