#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
ROOT=$PWD
WORK=${WORK:-$ROOT/.verify-work/comparator}
COMPARATOR_REV=c0c5a52d2aff92b457c3e5ed4a68c1ebc5795809
LANDRUN_REV=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
NANODA_REV=4c544ed4099c8227f07d5de77ad1e69fb0740a27
mkdir -p "$WORK"

fetch() {
  [ -d "$2/.git" ] || git clone -q "$1" "$2"
  git -C "$2" cat-file -e "$3^{commit}" 2>/dev/null || git -C "$2" fetch -q origin
  git -C "$2" checkout -q -f "$3"
}
fetch https://github.com/leanprover/comparator "$WORK/comparator" "$COMPARATOR_REV"
fetch https://github.com/Zouuup/landrun "$WORK/landrun" "$LANDRUN_REV"
fetch https://github.com/ammkrn/nanoda_lib "$WORK/nanoda_lib" "$NANODA_REV"
cp lean-toolchain "$WORK/comparator/lean-toolchain"
(cd "$WORK/comparator" && lake build comparator lean4export)
(cd "$WORK/landrun" && go build -o landrun ./cmd/landrun)
(cd "$WORK/nanoda_lib" && cargo build --release -q)

export COMPARATOR_LANDRUN="$WORK/landrun/landrun"
export COMPARATOR_LEAN4EXPORT="$WORK/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
export COMPARATOR_NANODA="$WORK/nanoda_lib/target/release/nanoda_bin"
BIN="$WORK/comparator/.lake/build/bin/comparator"

judge() {
  local cmd="lake env '$BIN' '$1'"
  if command -v systemd-run >/dev/null 2>&1 && systemd-run --user --scope -q true >/dev/null 2>&1; then
    systemd-run --user --wait --pipe --collect -q \
      --property=RestrictAddressFamilies=~AF_UNIX -p MemoryMax=40G -p MemorySwapMax=1G \
      -E PATH="$PATH" -E HOME="$HOME" -E COMPARATOR_LANDRUN="$COMPARATOR_LANDRUN" \
      -E COMPARATOR_LEAN4EXPORT="$COMPARATOR_LEAN4EXPORT" -E COMPARATOR_NANODA="$COMPARATOR_NANODA" \
      --working-directory "$ROOT" -- bash -c "$cmd" > "$2" 2>&1
  else
    echo "warning: no systemd user session; running without the AF_UNIX restriction and memory cap"
    bash -c "$cmd" > "$2" 2>&1
  fi
}

echo "== Comparator: Challenge vs FRD.Main (theorems frd, frdStrong) =="
if judge verification/comparator/config.json "$WORK/comparator.out"; then r=accepted; else r=rejected; fi
grep -vE "^(✔|ℹ|⚠)|Replayed|^warning:|^$|declaration uses|haveI|letI|The goal is|The difference|But this is|Note: This linter|Try this" "$WORK/comparator.out" | tail -15
echo "result: $r"
[ "$r" = accepted ] && grep -q "Your solution is okay!" "$WORK/comparator.out" || { echo "COMPARATOR CHECK FAILED"; exit 1; }

echo "== negative control: ChallengeControl (different statement) vs FRD.Main =="
if judge verification/comparator/config-control.json "$WORK/control.out"; then r=accepted; else r=rejected; fi
grep -vE "^(✔|ℹ|⚠)|Replayed|^warning:|^$|declaration uses|haveI|letI|The goal is|The difference|But this is|Note: This linter|Try this" "$WORK/control.out" | tail -6
echo "control: $r"
[ "$r" = rejected ] || { echo "CONTROL FAILED: a different statement was accepted"; exit 1; }
echo "COMPARATOR CHECK PASSED"
