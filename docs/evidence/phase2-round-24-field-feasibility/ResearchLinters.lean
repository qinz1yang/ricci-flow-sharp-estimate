import RicciFlowSharpEstimate
import AffineFieldChecks
import WarpOnlyPencilChecks
import HistoryStateChecks

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let prefixes := #["_private.AffineFieldChecks.", "_private.WarpOnlyPencilChecks.",
    "_private.HistoryStateChecks."]
  let decls := env.constants.toList.toArray.filterMap fun (n, _) =>
    if prefixes.any (fun p => p.isPrefixOf n.toString) then some n else none
  unless decls.size ≥ 30 do
    throwError "Research declaration selector is incomplete: {decls.size}"
  for declPrefix in prefixes do
    unless decls.any (fun n => declPrefix.isPrefixOf n.toString) do
      throwError "Missing probe declarations for {declPrefix}"
  for suffix in #[".negative_actual_density", ".trial_density_scale",
      ".no_constant_history_enclosure", ".calibration_det_pos_on_rectangle",
      ".history_defect_value"] do
    unless decls.any (fun n => n.toString.endsWith suffix) do
      throwError "Missing required research declaration {suffix}"
  for declName in decls do
    let info ← getConstInfo declName
    match info with
    | .defnInfo value =>
      if ← liftTermElabM <| Meta.isProp value.type then
        throwError "Definition {declName} has a proposition as its type"
    | .thmInfo value =>
      unless ← liftTermElabM <| Meta.isProp value.type do
        throwError "Theorem {declName} has a data-valued type"
    | _ => pure ()
  let linters ← liftCoreM <| Batteries.Tactic.Lint.getChecks true
    (some [`unusedArguments, `simpNF, `synTaut]) none
  unless linters.size = 3 do
    throwError "The three declaration linters were not all selected"
  let results ← liftCoreM <| Batteries.Tactic.Lint.lintCore decls linters
  if results.any (!·.2.isEmpty) then
    let message ← liftCoreM <| Batteries.Tactic.Lint.formatLinterResults results decls
      (groupByFilename := true) "in Round24ResearchProbes"
      (runSlowLinters := true) .low linters.size
    throwError message
