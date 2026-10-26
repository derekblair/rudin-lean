import Rudin.PMA.Chapter08.PowerSeriesFoundations
import Rudin.PMA.Chapter08.PowerSeriesDifferentiation
import Rudin.PMA.Chapter08.PowerSeriesCompatibility
import Rudin.PMA.Chapter08.Abel
import Rudin.PMA.Chapter08.DoubleSeries
import Rudin.PMA.Chapter08.Taylor
import Rudin.PMA.Chapter08.Operations
import Rudin.PMA.Chapter08.Exponential
import Rudin.PMA.Chapter08.Trigonometric
import Rudin.PMA.Chapter08.AlgebraicCompleteness
import Rudin.PMA.Chapter08.Orthogonality
import Rudin.PMA.Chapter08.FourierDefinitions
import Rudin.PMA.Chapter08.FourierConvergence
import Rudin.PMA.Chapter08.FourierParseval
import Rudin.PMA.Chapter08.GammaConsequences
import Rudin.PMA.Chapter08.GammaStirling

/-!
# PMA Chapter 8: Some Special Functions

The landed foundation and first-derivative modules are preserved. Reconciled
prior work completes PMA 8.1–8.6, including all derivative orders and factorial
coefficients; PowerSeriesCompatibility connects it to the landed interface.
PMA 8.7–8.8 establish trigonometric properties and algebraic completeness.
PMA 8.9–8.16 develop Fourier series using the native Chapter 6 Riemann integral;
PMA 8.17–8.22 develop the Gamma function through the all-real Stirling limit.
Every numbered node has a named contract and proof. The default build imports
Chapter08Audit for the complete 22-node coverage check and recursive
allowed-axiom audit.
-/
