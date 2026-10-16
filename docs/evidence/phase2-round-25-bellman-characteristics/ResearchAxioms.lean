import RicciFlowSharpEstimate
import QuadraticFluxProbe
import FreeCharacteristicProbe

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let prefixes := #["_private.QuadraticFluxProbe.", "_private.FreeCharacteristicProbe."]
  let decls := env.constants.toList.toArray.filterMap fun (n, _) =>
    if prefixes.any (fun p => p.isPrefixOf n.toString) then some n else none
  unless decls.size ≥ 30 do
    throwError "Research declaration selector is incomplete: {decls.size}"
  for declPrefix in prefixes do
    unless decls.any (fun n => declPrefix.isPrefixOf n.toString) do
      throwError "Missing probe declarations for {declPrefix}"
  for suffix in #[".full_flux_hasDerivAt", ".total_derivative_eq_partials",
      ".exists_zero_control_matrix", ".no_free_quadratic_branch_on_box",
      ".no_tight_interior_control_kernel", ".minimum_excludes_selected_box_tight_bellman",
      ".TightBellmanFieldFor"] do
    unless decls.any (fun n => n.toString.endsWith suffix) do
      throwError "Missing required research declaration {suffix}"
  logInfo m!"Selected {decls.size} research declarations, including private/generated declarations"
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for declName in decls.qsort Name.quickLt do
    let axioms ← liftCoreM <| collectAxioms declName
    unless axioms.all (allowed.contains ·) do
      throwError "Unapproved transitive axioms for {declName}: {axioms}"
    logInfo m!"{declName}: {axioms}"
    let info ← getConstInfo declName
    logInfo m!"TYPE {declName}: {info.type}"
