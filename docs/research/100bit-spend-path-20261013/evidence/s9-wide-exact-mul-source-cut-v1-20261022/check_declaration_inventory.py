from pathlib import Path
import json
R=Path(__file__).resolve().parent
i=json.loads((R/"evidence/charon/declaration-inventory.json").read_text())
assert i["has_errors"] is False
assert i["function_count"]==18 and i["type_count"]==4
need={"WideExact.mul","QM31.mul","QM31.add","QM31.sub","CM31.mul","CM31.add","CM31.sub","M31.add","M31.sub","M31.mul","M31.double","M31.reduce_u64","reduce_u64","mul_by_r","mul_u"}
d=i["required_transparent_declarations"]
assert set(d)==need,(set(d),need)
assert all(x["opacity"]=="Transparent" for x in d.values())
assert d["WideExact.mul"]["source_line"]==112
print("LLBC declaration inventory: PASS (raw LLBC intentionally omitted)")
