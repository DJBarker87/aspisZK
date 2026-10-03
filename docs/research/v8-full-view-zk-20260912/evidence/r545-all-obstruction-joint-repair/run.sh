#!/usr/bin/env bash
set -euo pipefail
cd /home/dombarker/project-offloads/aspis-r117-joint-privacy-schur-20261004-a
exec /usr/bin/time -v env \
  ASPIS_R17_C1_WITNESS_AUDIT=1 \
  ASPIS_R117_JOINT_STRESS=1 \
  ASPIS_R117_JOINT_STRESS_CASE=zero-low22 \
  ASPIS_R117_C1_CERT_PATH=/home/dombarker/project-offloads/aspis-r117-joint-privacy-schur-20261004-a/evidence/aggregate-all-schur/c1-total-schur.bin \
  ASPIS_R117_H1_CERT_PATH=/home/dombarker/project-offloads/aspis-r117-joint-privacy-schur-20261004-a/evidence/aggregate-all-schur/h1-cross-row.bin \
  ASPIS_R117_G_CERT_PATH=/home/dombarker/project-offloads/aspis-r117-joint-privacy-schur-20261004-a/evidence/aggregate-all-schur/g-baseline.bin \
  ASPIS_R117_SCHUR_CERT_PATH=/home/dombarker/project-offloads/aspis-r117-joint-privacy-schur-20261004-a/evidence/aggregate-all-schur/h1-g-schur.bin \
  /home/dombarker/project-offloads/aspis-r117-joint-privacy-schur-20261004-a/evidence/aggregate-all-schur/run/aspis-v8-performance-host \
  evidence/aggregate-all-schur/output-zero-low22
