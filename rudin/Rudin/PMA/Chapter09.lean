import Rudin.PMA.Chapter09.FirstHalfAudit
import Rudin.PMA.Chapter09.SecondHalfAudit
import Rudin.PMA.Chapter09.DeterminantsAudit
import Rudin.PMA.Chapter09.IntegralsAudit
import Rudin.PMA.AxiomAudit

/-!
# Rudin, *Principles of Mathematical Analysis* (3rd ed.)

## Chapter 9: Functions of Several Variables

Every definition, theorem, and corollary from this chapter is
formalized below in dependency order. Zero `sorry`s: anything
not yet proved is tracked in `QUEUE.md`, never as a `sorry` here.
-/

/-! Audit the whole imported chapter by module ownership, including generated
declarations outside the chapter namespace and the partial-audit helper. -/
run_cmd Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter09
