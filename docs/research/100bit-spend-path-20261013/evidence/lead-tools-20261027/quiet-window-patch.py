"""Insert a cross-stream quiet-window check at the top of a reservation script.

Usage: python3 quiet-window-patch.py <reservation.py>
If /home/dombarker/project-offloads/QUIET_WINDOW.json exists with {"until": <epoch>}
and now < until, the patched script writes an admission JSON with allowed=false and exits 0,
so workers wait-and-retry under local-lean rule 6. Idempotent.
"""
import sys, pathlib

p = pathlib.Path(sys.argv[1])
s = p.read_text()
TAG = "lead 2026-10-26: cross-stream quiet window"
if TAG in s:
    print("already patched", p)
    sys.exit(0)

block = '''# %s. If /home/dombarker/project-offloads/QUIET_WINDOW.json exists with {"until": <epoch seconds>}
# and now < until, refuse admission (workers wait-and-retry under local-lean rule 6).
import sys as _qw_sys, time as _qw_time, json as _qw_json, pathlib as _qw_pathlib
_qw = _qw_pathlib.Path("/home/dombarker/project-offloads/QUIET_WINDOW.json")
if _qw.exists():
    try:
        _qw_until = float(_qw_json.loads(_qw.read_text()).get("until", 0))
    except Exception:
        _qw_until = 0
    if _qw_time.time() < _qw_until:
        _qw_r = {"allowed": False, "reason": "quiet window until %%d (cross-stream timing gate)" %% int(_qw_until),
                 "quiet_window_until": int(_qw_until), "bounded_reserved_bytes": None, "requested_bytes": None}
        if len(_qw_sys.argv) > 1:
            _qw_pathlib.Path(_qw_sys.argv[1]).write_text(_qw_json.dumps(_qw_r) + "\\n")
        print(_qw_json.dumps(_qw_r))
        raise SystemExit(0)
''' % TAG

lines = s.split("\n")
i = 0
while i < len(lines) and (lines[i].startswith("import") or lines[i].startswith("from")
                          or lines[i].strip() == "" or lines[i].startswith("#")):
    i += 1
lines.insert(i, block)
p.write_text("\n".join(lines))
print("patched", p)
