/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/
import Lean

/-! Read-only documentation export from the compiled environment. This program
does not add declarations to FreeEntropy or replace the separate proof audit. -/

open Lean

private def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def strings (ns : Array Name) : Json :=
  toJson (ns.map Name.toString)

private def structuralRefs (ci : ConstantInfo) : Array Name :=
  match ci with
  | .inductInfo i => i.ctors.toArray ++ i.all.toArray
  | .ctorInfo i => #[i.induct]
  | .recInfo i => i.all.toArray ++ i.rules.toArray.flatMap
      (fun r => #[r.ctor] ++ r.rhs.getUsedConstants)
  | _ => #[]

private def location (env : Environment) (n : Name) : IO Json := do
  let (r, _) ← (findDeclarationRanges? n : CoreM (Option DeclarationRanges)).toIO
    { fileName := "<proof-catalog>", fileMap := default } { env := env }
  return match r with
  | none => Json.null
  | some r => Json.mkObj [
      ("line", toJson r.selectionRange.pos.line),
      ("column", toJson r.selectionRange.pos.column),
      ("start_line", toJson r.range.pos.line),
      ("start_column", toJson r.range.pos.column),
      ("end_line", toJson r.range.endPos.line),
      ("end_column", toJson r.range.endPos.column)]

unsafe def main (args : List String) : IO Unit := do
  let [outPath] := args
    | throw <| IO.userError "Expected output JSON path"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `FreeEntropy }] {}
    (leakEnv := true) (loadExts := true)
  let mut nodes : Array Json := #[]
  let mut modules : Array Json := #[]
  let mut seen : NameSet := {}
  let opts := ({} : Options).set `pp.width (100 : Nat)
    |>.set `pp.funBinderTypes true |>.set `pp.piBinderTypes true
  for idx in [:env.header.moduleData.size] do
    let mod := env.allImportedModuleNames[idx]!
    unless (`FreeEntropy).isPrefixOf mod do continue
    let data := env.header.moduleData[idx]!
    modules := modules.push <| Json.mkObj [
      ("name", toJson mod.toString),
      ("imports", strings (data.imports.map (·.module)))]
    for item in data.constants do
      if seen.contains item.name then continue
      seen := seen.insert item.name
      let some ci := env.checked.get.find? item.name
        | throw <| IO.userError s!"Missing kernel declaration: {item.name}"
      let some origin := env.getModuleIdxFor? ci.name
        | throw <| IO.userError s!"Missing defining module: {ci.name}"
      let definingModule := env.allImportedModuleNames[origin.toNat]!
      let statement ← PrettyPrinter.ppExprLegacy env {} {} opts ci.type
      let valueRefs := (ci.value? (allowOpaque := true)).map
        Expr.getUsedConstants |>.getD #[]
      nodes := nodes.push <| Json.mkObj [
        ("name", toJson ci.name.toString),
        ("kind", toJson (kind ci)),
        ("module", toJson definingModule.toString),
        ("statement", toJson statement.pretty),
        ("level_parameters", strings ci.levelParams.toArray),
        ("location", ← location env ci.name),
        ("type_references", strings ci.type.getUsedConstants),
        ("value_references", strings valueRefs),
        ("structural_references", strings (structuralRefs ci))]
  IO.FS.writeFile outPath <| (Json.mkObj [
    ("modules", toJson modules), ("declarations", toJson nodes)]).compress
  IO.println s!"Exported {nodes.size} compiled declarations from {modules.size} modules."
