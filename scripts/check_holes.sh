#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 - <<'PY'
import re, glob, sys
pat = re.compile(r'\bsorry\b|\badmit\b|\baxiom\b|\bunsafe\b|implemented_by|native_decide|\bextern\b|'
                 r'\bpartial\s+def\b|\bopaque\b|#eval\b|debug\.skipKernelTC|\bdecide\s*:=\s*true|'
                 r'Lean\.ofReduceBool|trustCompiler|\bcsimp\b', re.M)
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|class|inductive|example)\b\s*([^\s:({\[]*)', re.M)
files = ['FRD.lean', 'FinalCheck.lean'] + sorted(glob.glob('FRD/**/*.lean', recursive=True))
sorries, bad = [], []
for f in files:
    try: src = open(f, encoding='utf-8').read()
    except FileNotFoundError: continue
    out, depth, i = [], 0, 0
    while i < len(src):
        if src.startswith('/-', i): depth += 1; i += 2; out.append('  '); continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; out.append('  '); continue
        if not depth and src.startswith('--', i):
            j = src.find('\n', i); i = len(src) if j < 0 else j; continue
        out.append(src[i] if not depth else ('\n' if src[i] == '\n' else ' ')); i += 1
    code = ''.join(out)
    decls = [(m.start(), m.group(2) or m.group(1)) for m in decl.finditer(code)]
    for m in pat.finditer(code):
        name = '?'
        for pos, nm in decls:
            if pos <= m.start(): name = nm
            else: break
        line = code.count('\n', 0, m.start()) + 1
        (sorries if m.group(0) == 'sorry' else bad).append(f"{f}:{line}: {m.group(0)} [{name}]")
print(f"sorry occurrences in source: {len(sorries)}")
for s in sorries: print("  " + s)
print(f"other forbidden constructs: {len(bad)}")
for s in bad: print("  " + s)
sys.exit(1 if (sorries or bad) else 0)
PY
