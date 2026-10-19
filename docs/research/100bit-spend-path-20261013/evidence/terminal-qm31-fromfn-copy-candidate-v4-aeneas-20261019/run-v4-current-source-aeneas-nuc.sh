#!/usr/bin/env bash
set -euo pipefail

ATT=/home/dombarker/project-offloads/aspis-r1-terminal-current-source-candidate-20261019-v8
INPUT="$ATT/input"
OUT="$ATT/output"
LOG="$ATT/logs"
REC="$ATT/receipts"
CHARON=/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon
AENEAS=/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/bin/aeneas
CARGO=/home/dombarker/.cargo/bin/cargo
TARGET=/home/dombarker/project-offloads/aspis-r1-terminal-extraction-20261016/attempt-d/target
export PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin
export RUSTUP_TOOLCHAIN=nightly-2026-06-01 CARGO_BUILD_JOBS=1
export CARGO_PROFILE_RELEASE_OPT_LEVEL=3 CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true
export RUSTFLAGS='-C overflow-checks=yes' CARGO_TARGET_DIR="$TARGET" CARGO_NET_OFFLINE=true

mkdir -p "$OUT" "$LOG" "$REC"
cd "$INPUT"
python3 verify_merged.py > "$REC/input-validation.json"
tar -czf "$REC/v4-input-source-snapshot.tar.gz" \
  --exclude='provenance' --exclude='v4-overlay' -C "$ATT" input
sha256sum "$REC/v4-input-source-snapshot.tar.gz" > "$REC/v4-input-source-snapshot.sha256"
sha256sum "$INPUT/merged-source-manifest.json" "$INPUT/Cargo.toml" "$INPUT/Cargo.lock" \
  > "$REC/input-pins.sha256"

fresh_admission() {
  local stage="$1"
  python3 - "$REC/${stage}-admission.json" <<'PY'
import json, pathlib, re, subprocess, sys
out=pathlib.Path(sys.argv[1])
GiB=1024**3
def mib(key):
    for line in pathlib.Path('/proc/meminfo').read_text().splitlines():
        if line.startswith(key+':'): return int(line.split()[1])*1024
    return 0
def unit_rows(user):
    cmd=['systemctl']
    if user: cmd += ['--user']
    cmd += ['list-units','--type=scope','--state=running','--no-legend','--plain']
    try: lines=subprocess.check_output(cmd,text=True,stderr=subprocess.DEVNULL).splitlines()
    except Exception: return []
    rows=[]
    for line in lines:
        unit=line.split()[0]
        show=['systemctl']
        if user: show += ['--user']
        show += ['show',unit,'-p','MemoryMax','--value']
        try: raw=subprocess.check_output(show,text=True,stderr=subprocess.DEVNULL).strip()
        except Exception: raw='unknown'
        rows.append({'manager':'user' if user else 'system','unit':unit,'MemoryMax_bytes':int(raw) if raw.isdigit() else None})
    return rows
scopes=unit_rows(False)+unit_rows(True)
finite=sum(r['MemoryMax_bytes'] or 0 for r in scopes)
qemu=[]
for p in pathlib.Path('/proc').iterdir():
    if not p.name.isdigit(): continue
    try:
        if (p/'comm').read_text().strip().startswith('qemu-system'):
            argv=(p/'cmdline').read_bytes().split(b'\0')
            for i,x in enumerate(argv[:-1]):
                if x==b'-m':
                    s=argv[i+1].decode(errors='replace')
                    m=re.search(r'size=(\d+)k',s)
                    if m: qemu.append({'pid':int(p.name),'memory_bytes':int(m.group(1))*1024})
    except Exception: pass
qemu_reserve=sum(r['memory_bytes'] for r in qemu)
total=mib('MemTotal'); avail=mib('MemAvailable'); new=8*GiB; reserve=8*GiB
aggregate=finite+qemu_reserve+new+reserve
result={'MemTotal_bytes':total,'MemAvailable_bytes':avail,'active_scopes':scopes,
        'finite_scope_caps_bytes':finite,'active_qemu_reservations':qemu,
        'active_qemu_reserved_bytes':qemu_reserve,'new_scope_cap_bytes':new,
        'OS_and_control_reserve_bytes':reserve,'aggregate_reserved_with_new_scope_bytes':aggregate,
        'MemoryHigh_bytes':6*GiB,'MemoryMax_bytes':8*GiB,'MemorySwapMax_bytes':0,
        'admitted':avail>=14*GiB and aggregate<=total}
out.write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result))
if not result['admitted']: raise SystemExit('fresh aggregate admission rejected')
PY
}

run_stage() {
  local name="$1" unit="aspis-terminal-v4-$1-20261019"
  shift
  fresh_admission "$name"
  printf 'stage=%s argv=' "$name" > "$REC/$name.command.txt"
  printf '%q ' "$@" >> "$REC/$name.command.txt"
  printf '\n' >> "$REC/$name.command.txt"
  set +e
  systemd-run --user --scope --quiet --unit="$unit" \
    -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=128 \
    /usr/bin/time -v timeout 180s "$@" > "$LOG/$name.log" 2>&1
  local rc=$?
  set -e
  printf 'exit=%s\n' "$rc" > "$REC/$name.exit"
  grep -E 'Elapsed \(wall clock\)|Maximum resident set size|Swaps|Exit status' \
    "$LOG/$name.log" > "$REC/$name.time.txt" || true
  return "$rc"
}

run_stage charon "$CHARON" cargo --preset aeneas --mir built --sysroot default \
  --start-from crate::extraction_probe::terminal_qm31_probe \
  --dest-file "$OUT/Terminal-v4.llbc" -- \
  --manifest-path "$INPUT/Cargo.toml" --package aspis-r1-mask-extraction-probe \
  --features r0,pool-v1-kernel --no-default-features --release --lib --locked --offline
sha256sum "$OUT/Terminal-v4.llbc" > "$REC/Terminal-v4.llbc.sha256"

fresh_admission aeneas
python3 - "$OUT/Terminal-v4.llbc" "$OUT/Terminal-v4-M31-constructor-renamed.llbc" \
  "$REC/Terminal-v4-metadata-adapter.json" <<'PY'
import copy, hashlib, json, pathlib, sys
src,dst,receipt=map(pathlib.Path,sys.argv[1:])
data=json.loads(src.read_text()); translated=data['translated']
leaf=lambda x: x['item_meta']['name'][-1].get('Ident',[None])[0]
types=[]
for i,t in enumerate(translated['type_decls']):
    if t and leaf(t)=='M31' and t['item_meta'].get('source_text')=='pub struct M31(pub u32);': types.append((i,t))
assert len(types)==1, f'M31 type candidates={len(types)}'
ti,t=types[0]; span=t['item_meta']['span']
funs=[]
for i,f in enumerate(translated['fun_decls']):
    if f and leaf(f)=='M31' and f['item_meta'].get('source_text')=='pub struct M31(pub u32);' and f['item_meta'].get('span')==span:
        funs.append((i,f))
assert len(funs)==1, f'M31 constructor candidates={len(funs)}'
fi,f=funs[0]
assert f['item_meta']['attr_info'].get('rename') is None
f['item_meta']['attr_info']['rename']='M31_constructor'
dst.write_text(json.dumps(data,separators=(',',':')))
reverse=copy.deepcopy(data); reverse['translated']['fun_decls'][fi]['item_meta']['attr_info']['rename']=None
assert reverse==json.loads(src.read_text()), 'metadata edit changed more than one path'
h=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
rec={'kind':'same v10 one-field metadata alpha rename; dynamically located by unique source/name/span',
     'raw_llbc':str(src),'raw_llbc_sha256':h(src),'adapted_llbc':str(dst),'adapted_llbc_sha256':h(dst),
     'renamed_fun_index':fi,'renamed_fun_def_id':f['def_id'],'type_index':ti,'type_def_id':t['def_id'],
     'original_name':'aspis_r1_mask_extraction_probe::field::M31','new_name':'M31_constructor',
     'only_changed_path':f'translated.fun_decls[{fi}].item_meta.attr_info.rename',
     'deep_reverse_transform_equal':True}
receipt.write_text(json.dumps(rec,indent=2)+'\n'); print(json.dumps(rec,indent=2))
PY

run_stage aeneas "$AENEAS" -sequential -no-progress-bar -abort-on-error -backend lean \
  -namespace AspisR1SelectedMaskProbe -dest "$OUT/generated-current-v4" \
  -subdir AspisR1SelectedMaskProbe -split-files -emit-json -print-unknown-externals \
  -loops-to-rec "$OUT/Terminal-v4-M31-constructor-renamed.llbc"
sha256sum "$OUT/generated-current-v4/AspisR1SelectedMaskProbe/Funs.lean" \
  "$OUT/generated-current-v4/AspisR1SelectedMaskProbe/Types.lean" \
  "$OUT/generated-current-v4/AspisR1SelectedMaskProbe/FunsExternal_Template.lean" \
  "$OUT/generated-current-v4/AspisR1SelectedMaskProbe/TypesExternal_Template.lean" \
  "$OUT/generated-current-v4/translation.json" > "$REC/generated-v4.sha256"
grep -E '^axiom ' "$OUT/generated-current-v4/AspisR1SelectedMaskProbe/FunsExternal_Template.lean" \
  > "$REC/funs-external-axioms.txt" || true
grep -E '^axiom ' "$OUT/generated-current-v4/AspisR1SelectedMaskProbe/TypesExternal_Template.lean" \
  > "$REC/types-external-axioms.txt" || true
printf 'functions_axioms=%s\ntypes_axioms=%s\n' \
  "$(wc -l < "$REC/funs-external-axioms.txt" | tr -d ' ')" \
  "$(wc -l < "$REC/types-external-axioms.txt" | tr -d ' ')" > "$REC/external-template-counts.txt"
