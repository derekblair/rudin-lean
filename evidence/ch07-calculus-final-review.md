# Independent final review: PMA 7.16–7.17

Reviewer: root; author: taylor. **ACCEPT** on 2026-10-10.

Read the full 405-line canonical `Chapter07/Calculus.lean` at SHA256 `0bc805601a65a1261e944ae9d180b3cb0344c0d9484fc766f1d3df6c3411580d`. Its actual contracts match the independently accepted pre-proof types and the inventory. No hypothesis or conclusion was narrowed during implementation.

7.16 proves integrability through the native Darboux gap criterion and integral convergence through the native integral bound, then applies real and imaginary components. Arbitrary nondecreasing integrators, zero mass, singleton intervals, discontinuous integrable terms, and ordered conditional series remain permitted. Finite-sum integration gives the attached ordered-series conclusion without substituting unconditional summability.

7.17 uses the interval mean-value estimate on differences and one convergent anchor to construct the uniform function limit. A direct little-o argument proves its relative derivative at every point of the full closed interval, including endpoints. Derivative continuity, integrability, and a preexisting function limit are not assumed. Both complex and real targets instantiate the verified general normed-space argument. All four authored adversarial probes were read: imaginary discontinuous step, zero-mass integration, endpoint anchor with no ambient derivative, and an imaginary conditionally convergent ordered series.

Fresh independent `./lake-local env lean Chapter07CalculusRootProbe.lean` passed without warnings after routine client-only syntax repairs. Two theorem clients verify zero-mass behavior and complex uniform-limit existence with the full relative derivative conclusion; two additional checks expose the authored step and endpoint probes. Recursive audits cover 23 imported chapter declarations and two fresh client declarations, only propext, Classical.choice, and Quot.sound. The exact canonical hash is unchanged. No protected Chapter 5/6 source was modified.
