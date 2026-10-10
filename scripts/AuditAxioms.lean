import FRD
open Lean Elab Command

private def directSorry (ci : ConstantInfo) : Bool :=
  let uses (e : Expr) : Bool := (e.find? (fun s => s.isConstOf ``sorryAx)).isSome
  uses ci.type || (match ci with
    | .thmInfo v => uses v.value
    | .defnInfo v => uses v.value
    | .opaqueInfo v => uses v.value
    | _ => false)

private def userName (n : Name) : Name :=
  match n with
  | .str p s => if n.isInternal || s.startsWith "match_" || s.startsWith "proof_" then userName p else n
  | .num p _ => userName p
  | .anonymous => n

elab "#audit_axioms" : command => do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × List Name) := #[]
  let mut sorryDecls : Array Name := #[]
  let mut sorryDep : Nat := 0
  let mut userAxioms : Array Name := #[]
  let mut total : Nat := 0
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let ms := (env.header.moduleNames[idx.toNat]!).toString
    unless ms == "FRD" || ms.startsWith "FRD." do continue
    total := total + 1
    if ci.isAxiom then userAxioms := userAxioms.push n
    if directSorry ci then
      let u := userName n
      unless sorryDecls.contains u do sorryDecls := sorryDecls.push u
    let axs := (← liftCoreM <| Lean.collectAxioms n).toList
    if axs.contains ``sorryAx then sorryDep := sorryDep + 1
    let extra := axs.filter (fun a => !ok.contains a && a != ``sorryAx)
    unless extra.isEmpty do bad := bad.push (n, extra)
  logInfo m!"project constants: {total}"
  logInfo m!"declarations using sorry directly: {sorryDecls.size}"
  for d in sorryDecls.qsort (fun a b => a.toString < b.toString) do
    logInfo m!"  SORRY {d}"
  logInfo m!"constants depending on sorry (transitively): {sorryDep}"
  for a in userAxioms do logInfo m!"  AXIOM declared in project: {a}"
  for (n, extra) in bad do logInfo m!"  NONSTANDARD AXIOMS {n}: {extra}"
  let mut mainOk := true
  for thm in [`frd, `frdStrong] do
    if env.contains thm then
      let axs := (← liftCoreM <| Lean.collectAxioms thm).toList
      let axs := axs.toArray.qsort (fun a b => a.toString < b.toString) |>.toList
      logInfo m!"axioms of {thm}: {axs}"
      unless axs.all ok.contains do mainOk := false
    else
      logInfo m!"main theorem {thm}: MISSING"
      mainOk := false
  if sorryDecls.isEmpty && sorryDep == 0 && bad.isEmpty && userAxioms.isEmpty && mainOk then
    logInfo m!"AXIOM AUDIT OK: {total} constants, main theorems depend only on {ok}"
  else
    throwError "AXIOM AUDIT FAILED"

#audit_axioms
