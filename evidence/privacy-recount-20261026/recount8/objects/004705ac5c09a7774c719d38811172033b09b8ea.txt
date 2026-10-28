# Retry timing deviation

Reservation refusal50642 occurred2026-10-27T15:35:19.979157Z. Retry50643 was requested at15:37:58Z, approximately22seconds before the mandatory180seconds. The scope was admitted allowed:true/exit0 and the Lean target passed. This is a wait-rule deviation, not a memory cap bypass or proof failure. No unchanged proof rerun is justified by this scheduling error.

The private check.py now reads the newest recorded refusal UTC and requires at least180elapsedseconds before admission or ID consumption. It returns77 without launching/consuming an ID if the deadline has not passed. The root cause was relying on mental estimates of compile-free preparation time and a40second sleep. The deadline check replaces that estimate.
