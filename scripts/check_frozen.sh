#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
h=$(python3 - <<'PY'
import re, hashlib
src = open('FRD/Statement.lean', encoding='utf-8').read()
out, depth, i = [], 0, 0
while i < len(src):
    if src.startswith('/-', i): depth += 1; i += 2; continue
    if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
    if not depth and src.startswith('--', i):
        j = src.find('\n', i); i = len(src) if j < 0 else j; continue
    if not depth: out.append(src[i])
    i += 1
print(hashlib.sha256(re.sub(r'\s+', ' ', ''.join(out)).strip().encode()).hexdigest())
PY
)
python3 - <<'PY' || { echo "Challenge.lean does not match FRD/Statement.lean"; exit 1; }
import re, sys
def code(path):
    src = open(path, encoding='utf-8').read()
    out, depth, i = [], 0, 0
    while i < len(src):
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if not depth and src.startswith('--', i):
            j = src.find('\n', i); i = len(src) if j < 0 else j; continue
        if not depth: out.append(src[i])
        i += 1
    return re.sub(r'\s+', ' ', ''.join(out)).strip()
want = code('FRD/Statement.lean') + ' theorem frd : FRD := sorry theorem frdStrong : FRDStrong := sorry'
sys.exit(0 if code('Challenge.lean') == want else 1)
PY
if [ "${1:-check}" = snapshot ]; then echo "$h" > scripts/frozen_statement.sha256; echo "frozen: $h"; exit 0; fi
if [ "$h" = "$(cat scripts/frozen_statement.sha256)" ]; then echo "frozen statements unchanged; Challenge.lean = the same statements with open proofs"; else
  echo "FROZEN STATEMENTS CHANGED (FRD/Statement.lean)"; exit 1; fi
