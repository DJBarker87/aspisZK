# Permitted prefix retry review

The original prefix11 harness timed out after 180.003077 seconds at unwind33.
Resume8 changes the timeout to 900 seconds and adds taskset CPU affinity0-3,
as expressly permitted by ruling(i). It retains 6G/8G/swap0/Tasks64 and unwind33.
At the ten-minute review point the named CBMC prefix comparison was still active;
no new compilation scope was launched and no cap was raised. The explicit ruling
permits completion of this single retry. A timeout yields no equality or checked
counterexample. The next candidate is a split prefix01 assertion, never a third
identical prefix11 run.
