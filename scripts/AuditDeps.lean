import FRD
open Lean Elab Command

private def rootOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).getRoot.toString
  | none => "(current file)"

private def depClosure (env : Environment) (root : Name) : Except String NameSet := do
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    let some ci := env.find? n | throw s!"unknown constant {n}"
    let mut exprs : Array Expr := #[ci.type]
    let mut names : Array Name := #[]
    match ci with
    | .defnInfo v => exprs := exprs.push v.value
    | .thmInfo v => exprs := exprs.push v.value
    | .opaqueInfo v => exprs := exprs.push v.value
    | .inductInfo v => names := names ++ v.ctors.toArray ++ v.all.toArray
    | .ctorInfo v => names := names.push v.induct
    | .recInfo v =>
      names := names ++ v.all.toArray
      for r in v.rules do exprs := exprs.push r.rhs
    | _ => pure ()
    for e in exprs do names := names ++ e.getUsedConstants
    for u in names do
      unless visited.contains u do stack := stack.push u
  return visited

elab "#audit_deps" : command => do
  let env ← getEnv
  let allowed : List String := ["FRD", "Mathlib", "Batteries", "Aesop", "Qq", "Plausible",
    "ProofWidgets", "ImportGraph", "LeanSearchClient", "Cli", "Init", "Std", "Lean"]
  let mut ok := true
  for thm in [`frd, `frdStrong] do
    let Except.ok cl := depClosure env thm | throwError "closure failed for {thm}"
    let mut counts : Std.HashMap String Nat := {}
    for n in cl.toList do
      let r := rootOf env n
      counts := counts.insert r (counts.getD r 0 + 1)
    let sorted := counts.toList.toArray.qsort (fun a b => a.1 < b.1) |>.toList
    logInfo m!"dependency closure of {thm}: {cl.size} constants, by library: {sorted}"
    for (r, _) in sorted do
      unless allowed.contains r do
        ok := false
        logInfo m!"  NOT ALLOWED: library {r}"
  for st in [`FRD, `FRDStrong] do
    let Except.ok cl := depClosure env st | throwError "closure failed for {st}"
    let proj := cl.toList.filter (fun n => rootOf env n == "FRD" && n != st)
    logInfo m!"statement {st}: {cl.size} constants in its closure, project constants among them: {proj}"
    unless proj.isEmpty do ok := false
  if ok then logInfo m!"DEPENDENCY AUDIT OK: only this project, Mathlib, Mathlib's own dependencies and Lean core"
  else throwError "DEPENDENCY AUDIT FAILED"

#audit_deps
