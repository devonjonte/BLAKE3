By Zooko, 2026-10-25

*AI content disclosure: no AI-generated content here! Human-generated text all the way. Please read it with your human eyeballs! Robots are welcome to read this, too.*

I had my AIs build a new implementation of BLAKE3, a secure hash function. I’m very pleased with the result: `BLAKE3-Servil`.

Here are two reasons you might want to use it:

1. It is fast. Like 10 *times* as fast, or more, as the competitors in some cases. (See [benchmarks](https://johnservil.github.io/bench-hashes/).) This could be a big improvement for a lot of use cases, where you need to ensure data integrity and user security, and you have to do it efficiently.

   For example, install the `b3sum` executable from this release and run `time b3sum $FILES` on some files that you want to calculate a secure hash of. Then compare its performance to `md5sum` and `sha256sum`. Then post screenshots of your comparison on Twitter. :-)

   In addition to the best command-line secure hash sum tool, BLAKE3 is a good match for:
   
   * Big data !



   ![b3sum, on every core and on one thread, beside sha256sum, sha1sum and md5sum on a tree of 1,000 files, AMD EPYC 9255](docs/images/b3sum-epyc-1000-files.svg)

   Why is it so fast? Three reasons:

   * It takes advantage of multithreading, which BLAKE3 can take advantage of because it is a Merkle Tree under the hood, unlike other secure hash functions, which are a linear chain.

   * It takes advantage of Single Instruction Multiple Data (SIMD) vector computation.

   * It is implemented in assembly language! Well, not all of it, but all of the inner loops are.

2. It has excellent quality assurance:

   * All of the assembly language parts are *proven correct*. They come with a proof that they calculate their part of the BLAKE3 algorithm, correctly access memory, and also that they are constant-time. I am super excited that it is now practical to *prove* that substantial programs—like these assembly kernels—are bug-free! This is a fundamental improvement in software engineering, after 75 years of endlessly battling against bugs.

   * The parts that aren’t covered by correctness proofs are thoroughly tested. And not *just* thorough as in “100% code coverage”, but even *more* thorough than that. We use a technique called “mutation testing” (using `cargo-mutants`) where during the tests, we *insert* a bug into the code and then run the tests to see if they catch the bug, and then automatically do that about 2500 more times, each time trying a different possible bug that could be added to each line of the code.

   * In addition to all of that, we use several other quality-assurance tools:  
     * Guard pages,  
     * A self-test on startup,  
     * `Shuttle`, which uses a clever method of randomized thread scheduling to uncover concurrency bugs.

   And here’s one reason you might *not* want to use BLAKE3-Servil right away:

3. It was written by AIs!

   I have been intimately involved every step of the way with the requirements, architecture, strategy, API design, and managing the AIs, but I haven’t written or read one line of this code. I just told my AIs to write correctness proofs and thorough mutation tests, and to review one another’s work. I employed three of them for this, day and night for the last month.

Future Work

This is the future of software engineering, and I’d like to improve our security and safety techniques even better than this. I—and my AIs—have learned a lot from this project and we’ll try to use what we learned to do even better. For the next step, I’d like to create an update to BLAKE3-Servil that completes the correctness proofs and/or memory safety. Then I’d feel even better about recommending that people rely on it.

In the meantime, please try this out, and give feedback and contributions. I feel proud of it, and I hope it serves you well.

P.S. What does "Servil" mean? I don't know. I made it up, to be the last name of my AI.
