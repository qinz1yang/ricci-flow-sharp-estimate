#!/usr/bin/env python3
"""Replay native elaboration, declaration linting, and transitive axiom checks.

The required root build is enforced. Diagnostic drivers live in temporary scratch only.
"""

import argparse
import hashlib
import json
import platform
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    "RicciFlowSharpEstimate.Variational.Parameters",
    "RicciFlowSharpEstimate.Variational.PairFunctional",
    "RicciFlowSharpEstimate.Variational.Contacts",
    "RicciFlowSharpEstimate.Variational.FreeArc",
    "RicciFlowSharpEstimate.Variational.ObstacleProfile",
    "RicciFlowSharpEstimate.Analysis.ExponentialRemainder",
    "RicciFlowSharpEstimate.Variational.ObstaclePrimitives",
    "RicciFlowSharpEstimate.Variational.PairIteration",
    "RicciFlowSharpEstimate.Variational.Calibration",
    "RicciFlowSharpEstimate.Variational.OptimalValue",
    "RicciFlowSharpEstimate.Variational.PairRigidity",
    "RicciFlowSharpEstimate.Variational.ContactRegularity",
    "RicciFlowSharpEstimate.Variational.OptimizerRigidity",
]
OPTIONS = [
    "-j2", "-M4096", "-DautoImplicit=false", "-Dpp.unicode.fun=true",
    "-DmaxSynthPendingDepth=3", "-Dweak.linter.mathlibStandardSet=true",
    "-Dlinter.style.header.license=No license is granted by this file.",
]
SELECTOR = r"""
  let decls ← liftCoreM <|
    Batteries.Tactic.Lint.getDeclsInPackage `RicciFlowSharpEstimate
  for required in #[`RicciFlowSharpEstimate.Variational.existsUnique_capParameter,
      `RicciFlowSharpEstimate.Variational.capParameter_spec,
      `RicciFlowSharpEstimate.Variational.pairFunctional_sub_eq_integral_marginal,
      `RicciFlowSharpEstimate.Variational.pairFunctional_congr,
      `RicciFlowSharpEstimate.Variational.strictMonoOn_capParameter,
      `RicciFlowSharpEstimate.Variational.contact_bounds,
      `RicciFlowSharpEstimate.Variational.one_sub_upperContact_sq,
      `RicciFlowSharpEstimate.Variational.integral_freeExponential,
      `RicciFlowSharpEstimate.Variational.integral_two_mul_div_freeExponential,
      `RicciFlowSharpEstimate.Variational.obstacleLogProfile_admissible,
      `RicciFlowSharpEstimate.Variational.contact_separation_iff,
      `RicciFlowSharpEstimate.Analysis.exp_tangent_quadratic_lower,
      `RicciFlowSharpEstimate.Variational.obstacleTail_eq_free,
      `RicciFlowSharpEstimate.Variational.obstaclePrefix_eq_high,
      `RicciFlowSharpEstimate.Variational.pairFunctional_eq_intervalIntegral,
      `RicciFlowSharpEstimate.Variational.pairMarginal_obstacleLogProfile_low,
      `RicciFlowSharpEstimate.Variational.pairMarginal_obstacleLogProfile_free,
      `RicciFlowSharpEstimate.Variational.pairMarginal_obstacleLogProfile_high,
      `RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_le,
      `RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_eq,
      `RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_one,
      `RicciFlowSharpEstimate.Variational.pairRemainder_eq_zero_iff,
      `RicciFlowSharpEstimate.Variational.not_differentiableAt_obstacleLogProfile_lowerContact,
      `RicciFlowSharpEstimate.Variational.not_differentiableAt_obstacleLogProfile_upperContact,
      `RicciFlowSharpEstimate.Variational.pairFunctional_eq_obstacleLogProfile_iff,
      `RicciFlowSharpEstimate.Variational.pairFunctional_ge_closedForm,
      `RicciFlowSharpEstimate.Variational.pairFunctional_eq_closedForm_iff,
      `RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_lt_of_differentiableOn
    ] do
    unless decls.contains required do
      throwError "Missing required declaration {required}"
  if decls.size < 150 then
    throwError "Expected at least one hundred fifty project declarations"
""".lstrip("\n")
LINT_DRIVER = "import RicciFlowSharpEstimate\n\nopen Lean Elab Command in\nrun_cmd do\n" + SELECTOR + r"""
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
      (groupByFilename := true) "in RicciFlowSharpEstimate"
      (runSlowLinters := true) .low linters.size
    throwError message
""".lstrip("\n")
AXIOM_DRIVER = "import RicciFlowSharpEstimate\n\nopen Lean Elab Command in\nrun_cmd do\n" + SELECTOR + r"""
  logInfo m!"Selected {decls.size} project declarations, including private/generated declarations"
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for declName in decls.qsort Name.quickLt do
    let axioms ← liftCoreM <| collectAxioms declName
    unless axioms.all (allowed.contains ·) do
      throwError "Unapproved transitive axioms for {declName}: {axioms}"
    logInfo m!"{declName}: {axioms}"
""".lstrip("\n")
SIGNATURE_DRIVER = """import RicciFlowSharpEstimate

#check RicciFlowSharpEstimate.Variational.existsUnique_capParameter
#check RicciFlowSharpEstimate.Variational.capParameter_spec
#check RicciFlowSharpEstimate.Variational.capParameter_eq_one_iff
#print RicciFlowSharpEstimate.Variational.orderedTriangle
#print RicciFlowSharpEstimate.Variational.pairFunctional
#print RicciFlowSharpEstimate.Variational.pairMarginal
#print RicciFlowSharpEstimate.Variational.pairRemainder
#check RicciFlowSharpEstimate.Variational.pairFunctional_sub_eq_integral_marginal
#check RicciFlowSharpEstimate.Variational.pairRemainder_nonneg
#check RicciFlowSharpEstimate.Variational.pairFunctional_le_of_firstVariation_nonneg
#check RicciFlowSharpEstimate.Variational.pairFunctional_congr
#check RicciFlowSharpEstimate.Variational.strictMonoOn_capParameter
#print RicciFlowSharpEstimate.Variational.lowerContact
#print RicciFlowSharpEstimate.Variational.upperContact
#check RicciFlowSharpEstimate.Variational.contact_bounds
#check RicciFlowSharpEstimate.Variational.one_sub_upperContact_sq
#print RicciFlowSharpEstimate.Variational.freeExponential
#print RicciFlowSharpEstimate.Variational.freeLeftPrimitive
#print RicciFlowSharpEstimate.Variational.freeRightPrimitive
#check RicciFlowSharpEstimate.Variational.integral_freeExponential
#check RicciFlowSharpEstimate.Variational.integral_two_mul_div_freeExponential
#print RicciFlowSharpEstimate.Variational.obstacleExponential
#print RicciFlowSharpEstimate.Variational.obstacleLogProfile
#check RicciFlowSharpEstimate.Variational.obstacleExponential_eq_piecewise
#check RicciFlowSharpEstimate.Variational.obstacleLogProfile_admissible
#check RicciFlowSharpEstimate.Variational.obstacleLogProfile_one
#check RicciFlowSharpEstimate.Variational.contact_separation_iff
#check RicciFlowSharpEstimate.Analysis.exp_tangent_quadratic_lower
#print RicciFlowSharpEstimate.Variational.obstaclePrefix
#print RicciFlowSharpEstimate.Variational.obstacleTail
#check RicciFlowSharpEstimate.Variational.obstaclePrefix_eq_low
#check RicciFlowSharpEstimate.Variational.obstaclePrefix_eq_free
#check RicciFlowSharpEstimate.Variational.obstaclePrefix_eq_high
#check RicciFlowSharpEstimate.Variational.obstacleTail_eq_low
#check RicciFlowSharpEstimate.Variational.obstacleTail_eq_free
#check RicciFlowSharpEstimate.Variational.obstacleTail_eq_high
#check RicciFlowSharpEstimate.Variational.pairMarginal_eq_intervalIntegrals
#check RicciFlowSharpEstimate.Variational.pairMarginal_eq_zero_of_not_mem
#check RicciFlowSharpEstimate.Variational.integrable_pairMarginal
#check RicciFlowSharpEstimate.Variational.pairFunctional_eq_intervalIntegral
#check RicciFlowSharpEstimate.Variational.pairMarginal_obstacleLogProfile_low
#check RicciFlowSharpEstimate.Variational.pairMarginal_obstacleLogProfile_free
#check RicciFlowSharpEstimate.Variational.pairMarginal_obstacleLogProfile_high
#check RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_le
#check RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_eq
#check RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_one
#check RicciFlowSharpEstimate.Variational.pairRemainder_eq_zero_iff
#check RicciFlowSharpEstimate.Variational.hasDerivWithinAt_obstacleLogProfile_lowerContact_Iic
#check RicciFlowSharpEstimate.Variational.hasDerivWithinAt_obstacleLogProfile_lowerContact_Ici
#check RicciFlowSharpEstimate.Variational.hasDerivWithinAt_obstacleLogProfile_upperContact_Iic
#check RicciFlowSharpEstimate.Variational.hasDerivWithinAt_obstacleLogProfile_upperContact_Ici
#check RicciFlowSharpEstimate.Variational.not_differentiableAt_obstacleLogProfile_lowerContact
#check RicciFlowSharpEstimate.Variational.not_differentiableAt_obstacleLogProfile_upperContact
#check RicciFlowSharpEstimate.Variational.pairFunctional_eq_obstacleLogProfile_iff
#check RicciFlowSharpEstimate.Variational.pairFunctional_ge_closedForm
#check RicciFlowSharpEstimate.Variational.pairFunctional_eq_closedForm_iff
#check RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_lt_of_differentiableOn
"""


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    (output / "receipt.json").unlink(missing_ok=True)
    inputs = [ROOT / "RicciFlowSharpEstimate.lean", ROOT / "lakefile.toml",
              ROOT / "lean-toolchain", ROOT / "lake-manifest.json", Path(__file__).resolve()]
    inputs += [ROOT / (module.replace(".", "/") + ".lean") for module in MODULES]
    hashes = {str(path.relative_to(ROOT)): digest(path) for path in inputs}
    commands = []

    def run(label, command, silent=False):
        result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=180)
        (output / (label + ".txt")).write_text(result.stdout)
        commands.append({"label": label, "command": command, "exit_code": result.returncode,
                         "output_sha256": digest(output / (label + ".txt"))})
        if (result.returncode or "warning:" in result.stdout or "error:" in result.stdout
                or (silent and result.stdout.strip())):
            print(result.stdout, end="")
            raise RuntimeError(f"Native check failed: {label}")
        return result.stdout

    run("root-build", ["lake", "build"])
    version = run("lean-version", ["lake", "env", "lean", "--version"])
    lean_path = Path(run("lean-path", ["lake", "env", "which", "lean"]).strip())
    dependency_state = {}
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        package_path = ROOT / manifest["packagesDir"] / package["name"]
        revision = subprocess.check_output(
            ["git", "-C", str(package_path), "rev-parse", "HEAD"], text=True).strip()
        if revision != package["rev"]:
            raise RuntimeError(f"Dependency revision mismatch: {package['name']}")
        subprocess.run(["git", "-C", str(package_path), "diff", "--quiet", "HEAD"], check=True)
        dependency_state[package["name"]] = {"revision": revision, "tracked_sources_clean": True}
    for module in MODULES:
        run(module.rsplit(".", 1)[1].lower(),
            ["lake", "env", "lean", *OPTIONS, str(ROOT / (module.replace(".", "/") + ".lean"))],
            silent=True)
    with tempfile.TemporaryDirectory(prefix="math-target-") as scratch:
        for label, source, silent in [
            ("linters", LINT_DRIVER, True), ("axioms", AXIOM_DRIVER, False),
            ("signatures", SIGNATURE_DRIVER, False),
        ]:
            path = Path(scratch) / (label.capitalize() + ".lean")
            path.write_text(source)
            run(label, ["lake", "env", "lean", *OPTIONS, str(path)], silent=silent)
            commands[-1]["driver_sha256"] = digest(path)
    if hashes != {str(path.relative_to(ROOT)): digest(path) for path in inputs}:
        raise RuntimeError("Inputs changed during native validation")
    receipt = {
        "source_hashes": hashes, "platform": platform.platform(), "lean_version": version.strip(),
        "lean_binary_sha256": digest(lean_path), "dependencies": dependency_state,
        "commands": commands, "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "declaration_linters": ["unusedArguments", "simpNF", "synTaut"],
        "defLemma_replacement": "Native getConstInfo/Meta.isProp inspection of declaration kinds",
        "independent_review": "pending outer review; native evidence alone is not suite acceptance",
    }
    (output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"Native checks passed. Evidence: {output}")


if __name__ == "__main__":
    main()
