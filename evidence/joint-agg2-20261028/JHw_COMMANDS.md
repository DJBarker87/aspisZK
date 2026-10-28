# Exact admitted aggregation commands

Stage A, from `/home/dombarker/project-offloads/JHw_cache-20261028`:

```sh
python3 reservation_agg16.py JHw_A-reservation-0.json > JHw_A-barrier-0.log 2>&1
# Confirm exit 0 AND JSON allowed:true before uploading source/config.
systemd-run --user --scope -p MemoryHigh=14G -p MemoryMax=16G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host_agg16.py JHw_A.json > JHw_A-command.log 2>&1
/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake env lean -j1 -M15000 -DElab.async=false -o JHw_Wrapper.olean JHw_Wrapper.lean
```

Stage B, from `/home/dombarker/project-offloads/JHw_cache-20261028`:

```sh
python3 reservation_agg16.py JHw_B-reservation-0.json > JHw_B-barrier-0.log 2>&1
# Confirm exit 0 AND JSON allowed:true before uploading source/config.
systemd-run --user --scope -p MemoryHigh=14G -p MemoryMax=16G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host_agg16.py JHw_B.json > JHw_B-command.log 2>&1
/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake env lean -j1 -M15000 -DElab.async=false -o JHw_TX2.olean JHw_TX2.lean
```

Stage C, from `/home/dombarker/project-offloads/JHw_cache-20261028`:

```sh
python3 reservation_agg16.py JHw_C-reservation-0.json > JHw_C-barrier-0.log 2>&1
# Confirm exit 0 AND JSON allowed:true before uploading source/config.
systemd-run --user --scope -p MemoryHigh=14G -p MemoryMax=16G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host_agg16.py JHw_C.json > JHw_C-command.log 2>&1
/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake env lean -j1 -M15000 -DElab.async=false -o JHw_Joint.olean JHw_Joint.lean
```
