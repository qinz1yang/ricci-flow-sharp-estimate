import RicciFlowSharpEstimate
import FreeTraceChecks

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let prefixes := #["_private.FreeTraceChecks."]
  let decls := env.constants.toList.toArray.filterMap fun (n, _) =>
    if prefixes.any (fun p => p.isPrefixOf n.toString) then some n else none
  unless decls.size ≥ 35 do
    throwError "Research declaration selector is incomplete: {decls.size}"
  for declPrefix in prefixes do
    unless decls.any (fun n => declPrefix.isPrefixOf n.toString) do
      throwError "Missing probe declarations for {declPrefix}"
  for suffix in #[".density_add_jet_eq_square", ".freeTrace_axis_identity",
      ".traceHamiltonian_eq_potential_derivatives", ".tracePotential_hasDerivAt_f",
      ".tracePotential_hasDerivAt_b", ".tracePotential_hasDerivAt_r",
      ".tracePotential_hasDerivAt_v", ".traceHamiltonian_hasDerivAt",
      ".exists_negative_traceHamiltonian", ".round_state_and_probe",
      ".exists_negative_traceHamiltonian_at_round_state"] do
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
