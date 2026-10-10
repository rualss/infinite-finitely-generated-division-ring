#!/usr/bin/env bash
cap="${1:?usage: capped.sh <GiB> cmd args...}"; shift
if [ -z "${FRD_NO_CAP:-}" ] && command -v systemd-run >/dev/null 2>&1 \
   && systemd-run --user --scope -q true >/dev/null 2>&1; then
  exec systemd-run --user --scope -q -p MemoryMax="${cap}G" -p MemorySwapMax=1G "$@"
else
  exec "$@"
fi
