#!/usr/bin/env bash
set -uo pipefail
cd "$(dirname "$0")/.."
mkdir -p .verify-work
fail=0
echo "== 1. lake build (FRD, FinalCheck) =="
if lake build FRD > .verify-work/build.log 2>&1; then echo "build FRD: ok"; else echo "build FRD: FAILED"; grep -E "^error|error:" .verify-work/build.log | head -40; fail=1; fi
nsw=$(grep -c "declaration uses .sorry." .verify-work/build.log || true)
echo "sorry warnings in build log: $nsw"
[ "$nsw" = 0 ] || fail=1
if lake build FinalCheck > .verify-work/finalcheck.log 2>&1; then echo "build FinalCheck: ok"; else echo "build FinalCheck: FAILED"; grep -E "error" .verify-work/finalcheck.log | head -10; fail=1; fi
echo "== 2. source scan: sorry / forbidden constructs =="
./scripts/check_holes.sh || fail=1
echo "== 2b. imports: only Mathlib and this project =="
python3 - <<'PY' || fail=1
import glob, re, sys
bad = []
files = ['FRD.lean', 'FinalCheck.lean', 'Challenge.lean', 'verification/comparator/ChallengeControl.lean'] \
    + sorted(glob.glob('FRD/**/*.lean', recursive=True))
n = 0
for f in files:
    for i, line in enumerate(open(f, encoding='utf-8'), 1):
        m = re.match(r'\s*(?:public\s+)?import\s+(\S+)', line)
        if not m: continue
        n += 1
        mod = m.group(1)
        if not (mod == 'Mathlib' or mod == 'FRD' or mod.startswith('FRD.')): bad.append(f"{f}:{i}: import {mod}")
req = re.findall(r'^name\s*=\s*"([^"]+)"', open('lakefile.toml').read().split('[[require]]', 1)[1].split('[[lean_lib]]')[0], re.M)
nreq = open('lakefile.toml').read().count('[[require]]')
print(f"import lines: {n}; not Mathlib / not project: {len(bad)}")
for b in bad: print("  " + b)
print(f"lakefile [[require]] entries: {nreq} {req}")
sys.exit(1 if (bad or nreq != 1 or req != ['mathlib']) else 0)
PY
echo "== 3. axioms of every project constant =="
lake env lean scripts/AuditAxioms.lean 2>&1 | sed 's/^scripts\/AuditAxioms.lean:[0-9:]* *//' || fail=1
[ "${PIPESTATUS[0]}" = 0 ] || fail=1
echo "== 3b. dependency closure of the main theorems: only Mathlib (with its own dependencies) and Lean core =="
./scripts/capped.sh 20 lake env lean scripts/AuditDeps.lean 2>&1 | sed 's/^scripts\/AuditDeps.lean:[0-9:]* *//' | tr '\n' ' ' | sed 's/dependency closure/\ndependency closure/g; s/statement FRD/\nstatement FRD/g; s/DEPENDENCY AUDIT/\nDEPENDENCY AUDIT/; s/error:/\nerror:/g'; echo
[ "${PIPESTATUS[0]}" = 0 ] || fail=1
echo "== 4. frozen final statements =="
./scripts/check_frozen.sh || fail=1
if [ "${FULL:-0}" = 1 ]; then
  echo "== 5. kernel replay (leanchecker) of every project module =="
  python3 - > .verify-work/leanchecker.plan <<'PY'
import glob, re
mods = {}
for f in sorted(glob.glob('FRD/**/*.lean', recursive=True)) + ['FRD.lean', 'FinalCheck.lean']:
    src = open(f, encoding='utf-8').read()
    out, depth, i = [], 0, 0
    while i < len(src):
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if not depth and src.startswith('--', i):
            j = src.find('\n', i); i = len(src) if j < 0 else j; continue
        if not depth: out.append(src[i])
        i += 1
    code = [l.strip() for l in ''.join(out).splitlines() if l.strip()]
    mods[f[:-5].replace('/', '.')] = all(l.startswith('import ') for l in code)
def below(m, h): return m == h or m.startswith(h + '.')
heads = []
for m in sorted((m for m, agg in mods.items() if not agg), key=lambda m: (m.count('.'), m)):
    if not any(below(m, h) for h in heads): heads.append(m)
for m, agg in sorted(mods.items()):
    if agg: print('AGG', m)
for h in heads:
    grp = [m for m in mods if below(m, h)]
    print('HEAD', h, len(grp), ' '.join(sorted(grp)))
content = [m for m, agg in mods.items() if not agg]
missing = [m for m in content if not any(below(m, h) for h in heads)]
print('TOTAL', len(mods), 'CONTENT', len(content), 'MISSING', len(missing))
PY
  grep '^AGG' .verify-work/leanchecker.plan | sed 's/^AGG /aggregator (imports only, nothing to replay): /'
  n=0
  while read -r kind head cnt rest; do
    [ "$kind" = HEAD ] || continue
    if [ "$cnt" -gt 4 ]; then echo "leanchecker group too large ($cnt modules under $head): split or rename"; fail=1; continue; fi
    if ./scripts/capped.sh 40 lake env leanchecker "$head" > ".verify-work/leanchecker.$head.log" 2>&1; then n=$((n+cnt)); else echo "leanchecker FAILED: $head"; tail -5 ".verify-work/leanchecker.$head.log"; fail=1; fi
  done < .verify-work/leanchecker.plan
  grep '^TOTAL' .verify-work/leanchecker.plan
  grep -q 'MISSING 0$' .verify-work/leanchecker.plan || fail=1
  echo "leanchecker: $n modules replayed"
else
  echo "== 5. kernel replay skipped (run with FULL=1) ==";
fi
if [ $fail = 0 ] && [ "${FULL:-0}" = 1 ]; then echo "ALL CHECKS PASSED"
elif [ $fail = 0 ]; then echo "CHECKS 1-4 PASSED (item 5 not run)"
else echo "AUDIT: NOT COMPLETE"; exit 1; fi
