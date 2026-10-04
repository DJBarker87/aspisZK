#!/usr/bin/env bash
set -euo pipefail
cd /home/dombarker/project-offloads/aspis-r117-actual-seed1-schur-20261004-a
exec /usr/bin/time -v env \
  ASPIS_R17_C1_WITNESS_AUDIT=1 \
  ASPIS_R117_C1_CERT_PATH=/home/dombarker/project-offloads/aspis-r117-actual-seed1-schur-20261004-a/evidence/actual-seed1-schur/c1-total-schur.bin \
  ASPIS_R117_H1_CERT_PATH=/home/dombarker/project-offloads/aspis-r117-actual-seed1-schur-20261004-a/evidence/actual-seed1-schur/h1-cross-row.bin \
  ASPIS_R117_G_CERT_PATH=/home/dombarker/project-offloads/aspis-r117-actual-seed1-schur-20261004-a/evidence/actual-seed1-schur/g-baseline.bin \
  ASPIS_R117_SCHUR_CERT_PATH=/home/dombarker/project-offloads/aspis-r117-actual-seed1-schur-20261004-a/evidence/actual-seed1-schur/h1-g-schur.bin \
  /home/dombarker/project-offloads/aspis-r117-actual-seed1-schur-20261004-a/evidence/actual-seed1-schur/run/aspis-v8-performance-host \
  evidence/actual-seed1-schur/output-seed1
