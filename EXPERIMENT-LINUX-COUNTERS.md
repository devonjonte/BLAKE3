# Experimental shared Linux counters

Runtime source e54b6f2 is an instrument diagnostic, not an accepted reliability
fix or a change to upstream's frozen benchmark0.10.0. Hashing is unchanged.
The user’s optimization prerequisite remains NO-GO.

Tests on this native64-bit Intel hybrid host establish live P/E counter
classification, basic perf attribute/group contracts and retained-record
agreement. Hardware availability and these tests do not establish generic
Linux portability or benchmark reliability. In particular, x32 ABI gating and
counter-cache ownership after fork without exec need review; tested harness
children start through exec. Counted cycles/instructions exclude kernel/HV;
PMU running time includes kernel execution while scheduled. Rates approximate
MHz on long batches. Wall times and counters are unscaled.

Plan, source identities, all32 fresh processes and test logs:
https://github.com/devonjonte/bench-hashes/tree/candidate/devon-measurement-trust/audit/results/linux-counter-diagnostic

Upstream adoption needs Zooko's recorded freeze decision and a new release.
Keep experimental source/evidence separate from the frozen instrument.
