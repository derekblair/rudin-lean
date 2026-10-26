#!/usr/bin/env python3
"""Regression checks for module ownership and fail-closed axiom auditing.

Fixtures live only in a temporary .lake directory and are removed on exit. The
negative fixture deliberately depends on an unapproved synthetic axiom; it must
be rejected by the audit even though that axiom belongs to another module.
Chapter 8's actual audit wrapper is also checked against lost probe imports and
an ownership-selector mutation omitting a required generated declaration.
One-pin deletions from the actual Chapter 8 and Chapter 11 wrappers must fail
even though the affected modules and all their declarations remain imported.
"""

from pathlib import Path
import os
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1] / "rudin"


def main():
    subprocess.run(["lake", "build", "Rudin.PMA.Chapter08Audit",
                    "Rudin.PMA.Chapter11Audit"], cwd=ROOT, check=True)
    lean_prefix = subprocess.check_output(
        ["lake", "env", "lean", "--print-prefix"], cwd=ROOT, text=True).strip()
    lean_path = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True).strip()
    with tempfile.TemporaryDirectory(prefix="axiom-audit-", dir=ROOT / ".lake") as raw:
        scratch = Path(raw)
        env = dict(os.environ)
        # Invoke the pinned Lean directly: `lake env` would prepend its build
        # paths again and prevent the scratch mutant from shadowing AxiomAudit.
        env["LEAN_PATH"] = str(scratch) + os.pathsep + lean_path

        def lean(module, source, *, compile_module=False, expected_error=None,
                 rejection_label=None):
            path = scratch.joinpath(*module.split(".")).with_suffix(".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
            command = [str(Path(lean_prefix) / "bin" / "lean"),
                       "--root", str(scratch), str(path)]
            if compile_module:
                command += ["-o", str(path.with_suffix(".olean"))]
            result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if expected_error is None:
                if result.returncode:
                    raise RuntimeError(f"{module} failed:\n{result.stdout}")
            elif result.returncode == 0 or expected_error not in result.stdout:
                raise RuntimeError(f"{module} did not reject as expected:\n{result.stdout}")
            if rejection_label is not None:
                diagnostic = next(line for line in result.stdout.splitlines()
                                  if expected_error in line)
                print(f"{rejection_label}: rejected (exit {result.returncode}); "
                      f"{diagnostic}", flush=True)
            return result.stdout

        lean("AuditFixture.Generated", """import Rudin.PMA.AxiomAudit
namespace OutsideNamespace
inductive Marker where | item
def step : Nat → Nat | 0 => 0 | n + 1 => n
theorem step_zero : step 0 = 0 := step.eq_1
private theorem hidden : True := True.intro
end OutsideNamespace
""", compile_module=True)
        lean("AuditFixture", """import AuditFixture.Generated
theorem AnotherNamespace.root : True := True.intro
""", compile_module=True)
        output = lean("PositiveAudit", """import AuditFixture
run_cmd do
  let env ← Lean.getEnv
  let hidden := env.constants.fold (init := #[]) fun names name _ =>
    if Lean.privateToUserName name == `OutsideNamespace.hidden then names.push name else names
  if hidden.size != 1 then throwError "Expected exactly one private fixture theorem."
  Rudin.PMA.Audit.checkModuleAxioms `AuditFixture
    (#[`OutsideNamespace.step.eq_1, `OutsideNamespace.Marker.item, `AnotherNamespace.root] ++ hidden)
""")
        for expected in ["Axiom audit module AuditFixture.Generated:",
                         "OutsideNamespace.step.eq_1", "OutsideNamespace.hidden",
                         "no forbidden axioms"]:
            if expected not in output:
                raise RuntimeError(f"Missing positive coverage {expected}:\n{output}")
        lean("CurrentAudit", """import Rudin.PMA.AxiomAudit
private theorem Elsewhere.current : True := True.intro
run_cmd do
  let env ← Lean.getEnv
  let hidden := env.constants.fold (init := #[]) fun names name _ =>
    if Lean.privateToUserName name == `Elsewhere.current then names.push name else names
  if hidden.size != 1 then throwError "Expected exactly one current private theorem."
  Rudin.PMA.Audit.checkModuleAxioms `CurrentAudit hidden
""")
        lean("MissingAudit", """import Rudin.PMA.AxiomAudit
run_cmd Rudin.PMA.Audit.checkModuleAxioms `NotImported
""", expected_error="is not imported or current")
        lean("EmptyFixture", "import Rudin.PMA.AxiomAudit\n", compile_module=True)
        lean("EmptyAudit", """import EmptyFixture
run_cmd Rudin.PMA.Audit.checkModuleAxioms `EmptyFixture
""", expected_error="found no declarations")
        lean("EmptyAuditAllowed", """import EmptyFixture
run_cmd Rudin.PMA.Audit.checkModuleAxioms `EmptyFixture (allowEmpty := true)
""")
        lean("NonemptyAuditAllowed", """import AuditFixture
run_cmd Rudin.PMA.Audit.checkModuleAxioms `AuditFixture
  #[`OutsideNamespace.step.eq_1] (allowEmpty := true)
""", expected_error="Axiom audit coverage regression: module AuditFixture owns",
             rejection_label="Nonempty module cannot bypass pin coverage with allowEmpty")
        lean("CoverageAudit", """import AuditFixture
run_cmd Rudin.PMA.Audit.checkModuleAxioms `AuditFixture #[`Missing.declaration]
""", expected_error="coverage regression")
        lean("UnapprovedDependency", """import Rudin.PMA.AxiomAudit
axiom Unrelated.unapproved : False
""", compile_module=True)
        lean("NegativeFixture", """import UnapprovedDependency
theorem OutsideNamespace.bad : False := Unrelated.unapproved
""", compile_module=True)
        lean("NegativeAudit", """import NegativeFixture
run_cmd Rudin.PMA.Audit.checkModuleAxioms `NegativeFixture #[`OutsideNamespace.bad]
""", expected_error="Forbidden axioms in OutsideNamespace.bad")

        # Keep the real module identity, imports, contracts, and audit calls.
        # Only the specified scratch mutation changes between each test.
        # Lean selects a package root once, so a scratch Rudin directory must
        # expose every imported Rudin artifact, not only the mutated module.
        built_rudin = ROOT / ".lake/build/lib/lean/Rudin"
        for artifact in built_rudin.rglob("*"):
            if artifact.is_file():
                target = scratch / "Rudin" / artifact.relative_to(built_rudin)
                target.parent.mkdir(parents=True, exist_ok=True)
                if not target.exists() and not target.is_symlink():
                    target.symlink_to(artifact)
        chapter_module = "Rudin.PMA.Chapter08Audit"
        chapter_source = (ROOT / "Rudin/PMA/Chapter08Audit.lean").read_text()
        output = lean(chapter_module, chapter_source)
        counts = []
        for module in ["Rudin.PMA.Chapter08", "Rudin.PMA.Chapter08Probes"]:
            matches = re.findall(
                rf"Axiom audit for {re.escape(module)}: checked (\d+) declarations", output)
            if len(matches) != 1:
                raise RuntimeError(f"Missing/ambiguous real Chapter08 coverage:\n{output}")
            counts.append(int(matches[0]))
        if sum(counts) < 535:
            raise RuntimeError(f"Real Chapter08 coverage regressed below 535: {counts}")
        print(f"Chapter08 real-wrapper control: exit 0; {counts[0]} chapter + "
              f"{counts[1]} probe declarations = {sum(counts)}.", flush=True)

        chapter11_module = "Rudin.PMA.Chapter11Audit"
        chapter11_source = (ROOT / "Rudin/PMA/Chapter11Audit.lean").read_text()
        output = lean(chapter11_module, chapter11_source)
        counts = re.findall(
            r"Axiom audit for Rudin\.PMA\.Chapter11: checked (\d+) declarations", output)
        pins = re.findall(
            r"Axiom audit coverage: (\S+) \(module Rudin\.PMA\.Chapter11\.[^)]+\)", output)
        if counts != ["794"] or len(pins) != 24 or len(set(pins)) != 24:
            raise RuntimeError(f"Real Chapter11 coverage changed:\n{output}")
        print("Chapter11 real-wrapper control: exit 0; 794 declarations; "
              "24 distinct ownership pins.", flush=True)

        for module, source, pin, owner in [
            (chapter11_module, chapter11_source,
             "Rudin.PMA.Chapter11.SecondHalf.partitionStep_integral",
             "Rudin.PMA.Chapter11.Darboux"),
            (chapter_module, chapter_source,
             "Rudin.PMA.Chapter08.abelPowerSeries", "Rudin.PMA.Chapter08.Abel"),
        ]:
            pin_line = f"    `{pin},\n"
            if source.count(pin_line) != 1:
                raise RuntimeError(f"Expected exactly one pin line for {pin} to delete.")
            lean(module, source.replace(pin_line, "", 1),
                 expected_error=f"Axiom audit coverage regression: module {owner}",
                 rejection_label=f"{module} deleted sole pin {pin}")

        probe_import = "import Rudin.PMA.Chapter08.ExponentialProbes\n"
        if chapter_source.count(probe_import) != 1:
            raise RuntimeError("Expected exactly one ExponentialProbes import to mutate.")
        lean(chapter_module, chapter_source.replace(probe_import, "", 1),
             expected_error="Axiom audit coverage regression: "
                            "Rudin.PMA.Chapter08.FidelityProbes.",
             rejection_label="Chapter08 dropped ExponentialProbes import")

        checker_module = "Rudin.PMA.AxiomAudit"
        checker_source = (ROOT / "Rudin/PMA/AxiomAudit.lean").read_text()
        selector = ("if modulePrefix.isPrefixOf (declarationModule env name) "
                    "then names.push name else names")
        if checker_source.count(selector) != 1:
            raise RuntimeError("Expected exactly one module-ownership selector to mutate.")
        mutant_selector = ("if modulePrefix.isPrefixOf (declarationModule env name) && "
                           "name != `Equiv.boolProdNatEquivNat.eq_1 "
                           "then names.push name else names")
        # Unlink all borrowed checker artifacts before Lean writes any output
        # (including possible .olean.private/.olean.server companion files).
        # Other project artifacts remain read-only symlink inputs.
        checker_copy = scratch.joinpath(*checker_module.split("."))
        for artifact in checker_copy.parent.glob(checker_copy.name + ".*"):
            if artifact.is_symlink():
                artifact.unlink()
        lean(checker_module, checker_source.replace(selector, mutant_selector, 1),
             compile_module=True)
        lean(chapter_module, chapter_source,
             expected_error="Axiom audit coverage regression: "
                            "Equiv.boolProdNatEquivNat.eq_1",
             rejection_label="Chapter08 excluded generated declaration")
    print("Axiom-audit regression checks passed: imported/generated/private/current "
          "declarations, submodules, missing/empty modules, nonempty allowEmpty guard, "
          "required coverage, and "
          "transitive forbidden-axiom rejection; real Chapter08 scope-loss mutations "
          "and Chapter08/Chapter11 one-pin deletions rejected.")


if __name__ == "__main__":
    main()
