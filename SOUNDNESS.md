[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Formal Verification in mlkem-native: Scope, Assumptions, Risks

This document describes the scope, assumptions and risks of the formal verification
efforts around mlkem-native.

The parts of the analysis pertaining to HOL Light and s2n-bignum are largely shared with
the corresponding [^s2n-bignum-soundness].

## Overview

Formal verification is never absolute. Every verification effort links formal objects --
specifications and models -- to informal, real-world requirements and systems. This document
maps out what is proved about mlkem-native, what is assumed, and where the gaps and risks lie.

Our goal is to provide evidence rooted in formal reasoning for the statement that
"mlkem-native implements the [^FIPS203] standard and does not leak secrets through timing variations".

The narrative for the argument is the following, which is common in formal verification:
- [Informal] Here is the real physical system, in all its complexity.
- [Formal] Here is a formal model of the real system which we believe approximates its behavior.
- [Formal] Here is how we can formally specify the behavior of this formal model.
- [Formal] Here is how we formally prove the formal specification.
- [Informal] Here is why we think this approximates the desired properties of the real system.

Diagrammatically, this can be depicted as follows:

```

                                                  "Here is how we can formally specify
                                                   the behavior of mlkem-native w.r.t.
                                                   the machine's formal model."

         Informal                                              Formal
  ┌─────────────────────┐                             ┌─────────────────────────┐
  │                     │            Gap A            │                         │
  │  Desired behavior   │<· · · · · · · · · · · · · ·>│   Formal specification  │
  │  of actual system   │   Is this what we wanted?   │                         │
  │                     │                             │                         │
  └─────────────────────┘                             └────────────▲────────────┘
           ^                                                       │
           :                                    Is the argument    │
           :                                    sound?             │  "Here is how we formally
           : GOAL                                                  │   prove mlkem-native's
           :                                         Gap C: prover │   formal specification."
           :                                         trust (TCB)   │
           v                                                       │
  ┌─────────────────────┐                             ┌────────────┴────────────┐
  │                     │            Gap B            │                         │
  │  Actual system      │<· · · · · · · · · · · · · ·>│     Formal model of     │
  │                     │   Is this how the system    │     system and code     │
  │  Code running on    │   behaves?                  │  Code representation +  │
  │  real hardware      │                             │  execution semantics    │
  └─────────────────────┘                             └─────────────────────────┘

  "Here's the real system."                           "Here's how we think it can
                                                       be formally approximated."

```

This methodology introduces three fundamental soundness gaps:
- Gap A: Does the formal specification capture what we want to say about the real system?
- Gap B: Is the formal model a faithful reflection of the real system?
- Gap C: Is the formal argument trustworthy for why the formal model satisfies its specification?

For mlkem-native, this structure is instantiated twice -- once for each verification
stack.

- **[^CBMC]** for the C code: memory safety, type safety, and absence of undefined behavior.
- **[^HOL-Light] + [^s2n-bignum]** for the assembly backends: functional correctness, memory safety, and secret-independent
  execution.

```
         Informal                            Formal
  ┌─────────────────────┐          ┌──────────────────────────┐
  │                     │          │                          │
  │  ML-KEM spec        │          │  CBMC          HOL Light │
  │  (FIPS 203),        │          │  contracts     specs     │
  │  constant-time      │   Gap A  │  (C funcs)      (ASM)    │
  │  requirements,      │<· · · · >│     :             :      │
  │  ABI, ...           │          │     :             :      │
  │                     │          │     :             :      │
  │                     │          │     :             :      │
  └─────────────────────┘          └─────▲─────────────▲──────┘
                                         │             │
                                   Gap C │        Gap C│
                                         │             │
                                   CBMC +│      HOL Light kernel
                             SMT solvers │             │
                                         │             │
  ┌─────────────────────┐          ┌─────┴─────────────┴─────┐
  │                     │          │                         │
  │  Compiled binary    │          │                         │
  │  on real hardware   │   Gap B  │  CBMC's C      ISA      │
  │                     │<· · · · >│  semantics    model     │
  │  (+ CPU errata,     │          │  model      (arm.ml/    │
  │   physical faults,  │          │             x86.ml)     │
  │   reassembly risk)  │          │                         │
  └─────────────────────┘          └─────────────────────────┘
```

---

## Gap A: Do the formal specifications match actual requirements?

This is the gap between what we *specify* and what users and applications actually *need*.
It has multiple facets, including: Whether all system components are covered by specification (breadth),
whether the specifications are strong enough (depth), whether they faithfully capture the informal requirements
(faithfulness), and whether they compose to a claim about the whole system (consistency).

### A1. Coverage: Breadth

Which components of the system are captured by formal specification? The primary risk is
that our coverage claims are wrong -- that a C or assembly function slips through without
a specification, or that an unspecified component is incorrect.

**What is covered.**

- All C code in the core library has CBMC contracts.
- All AArch64 assembly routines have HOL Light specifications.
- All x86_64 assembly routines have HOL Light specifications.

**What is NOT covered.**

- **x86_64 intrinsics-based C code.** The native Keccak-F1600 implementations for
  x86_64 are written in intrinsics and not covered by any specification.
- **Other backends** (RISC-V RVV, experimental Armv8.1-M MVE, PowerPC):
  these are not covered by specification.

The full test suite (functional tests, KAT, ACVP, unit tests) validates functional
correctness empirically across all platforms and configurations, but there is currently
no automatic check that every C function has a CBMC contract or that every assembly
routine has a HOL Light proof. A function could slip through without specification.

**Potential improvements.**
- Add automatic proof coverage check to CI. (TODO: Ref tracking issue)
- Replace all intrinsics-based code with pure assembly, bringing it into the scope of
  HOL Light verification. (TODO: Ref tracking issue)
- Extend assembly verification to all backends. (TODO: Ref tracking issue)

### A2. Coverage: Depth

Do the specifications have the desired depth? The risk is that undesired behavior occurs
which is outside the scope of specification.

Currently, we aim for mlkem-native to be **functionally correct** (the code computes the
right answer as per FIPS 203) and **constant-time** (no secret-dependent timing variation).

**Assembly (HOL Light).** With one exception, the ASM specifications capture functional
correctness, memory safety, and secret-independent execution. The one exception remaining is
rejection sampling: the native implementations for this function only have functional
correctness specifications, but no specifications of memory safety (the functions are safely
variable-time, so no constant-time proofs are needed).

**C code (CBMC).** Our use of CBMC focuses on **memory safety and type safety** -- absence
of undefined behavior including out-of-bounds access, integer overflow, null pointer
dereference, division by zero, undefined shifts, and lossy type conversions. The proofs
also capture limited aspects of functional behavior in simple cases -- for example,
coefficient bounds after arithmetic operations, or the functional specification of
`mlk_ct_memcmp`. See [`proofs/cbmc/Makefile.common`](proofs/cbmc/Makefile.common) for the
full list of checked classes of undefined behavior.

The CBMC proofs do **not** currently cover:

- **Functional correctness.** There is no machine-checked proof that the C code computes
  the right answer per FIPS 203.
- **Constant-time execution.** Side-channel resistance at the C level is not formally
  proved.

These gaps are mitigated in complementary ways. The full test suite (functional tests, KAT,
ACVP, unit tests) validates functional correctness empirically across all platforms and
configurations. For arithmetic correctness specifically, the most subtle bugs in ML-KEM
implementations are rare overflows in the optimized polynomial arithmetic -- precisely the
kind of bug that the type-safety and integer-overflow proofs are designed to catch: the CBMC
contracts track coefficient bounds through the arithmetic pipeline, and overflow in
intermediate computations would be flagged as undefined behavior. Constant-time properties
are tested empirically using valgrind with a variable-latency patch across many compilers
(GCC 4.8–15, Clang 14–21) and optimization levels (-O0 through -Ofast), and the C code
uses value barriers to prevent harmful compiler optimizations.

**Potential improvements.**
- Add memory-safety proof for rejection sampling routines. (TODO: Ref tracking issue)
- Introduce additional verification tooling that allows us to express functional correctness
  and constant-time properties for the C code. (TODO: Ref tracking issue)

### A3. Specification faithfulness

For the specifications that do exist, does their formal meaning capture their intent? The
risk is that a specification does not express what we informally intend it to express.

**Correctness.** The informal intent is to express that the top-level
API behaves as specified by NIST's ML-KEM standard FIPS 203. As we do not yet address
functional correctness at the C level, there is no formal specification of ML-KEM as a
whole in mlkem-native. In our current setting -- capturing functional behavior only at the
assembly level -- faithfulness requires that the HOL Light correctness specification style
faithfully captures program behavior, and that the abstract HOL functions used in the
specifications (e.g., the Number Theoretic Transform) are faithful representations of the
mathematical functions in the standard.

**Constant-time.** The informal intent is that mlkem-native does not
leak secrets through timing side channels. Since we only capture constant-time properties
at the assembly level, faithfulness requires that the HOL Light constant-time specification
style faithfully captures constant-time execution.

The s2n-bignum formal model approximates constant-time'ness as follows: It introduces the
notion of *microarchitectural events* that flag uses of instructions with potentially
data-dependent timing (e.g., integer division). The constant-time proofs then establish
that (a) the sequence of instructions executed and all memory addresses accessed are independent
of secret inputs, and that (b) no variable-timing microarchitectural events occur.

The formal notion of constant-time'ness used in s2n-bignum does not and cannot guarantee
that the hardware executes those instructions in constant time: microarchitectural effects
(variable-latency instructions, Hertzbleed-style frequency scaling) could still leak
information. Some hardwaren provides opt-in guarantees for a listed set of instructions -- ARM's DIT (Data Independent
Timing, Armv8.4-A onwards) and Intel's DOITM (Data Operand Independent Timing Mode, Ice Lake onwards) -- but even with
these enabled, coverage is limited to specific instruction sets, and power- or frequency-based side channels remain
outside scope. See [^s2n-bignum-soundness] for full details.

**Safety.** For the bulk of the CBMC specifications which do not capture
functional correctness, memory- and type-safety are implicit in the CBMC configuration
and not explicitly stated in the CBMC contracts. Additional clauses in the CBMC contracts
(such as memory assumptions and footprint) need not be human-validated except for the top-level
API, since their adequacy is judged by the machine-checked compositionality against their
call-sites. The fidelity of CBMC specifications therefore reduces to whether the top-level
CBMC specifications capture the footprint and assumptions of the top-level FIPS 203 API,
and whether CBMC is correctly configured to include memory- and type-safety implicitly in
each function contract.

All specifications are written in a high-level mathematical style (HOL Light) or a simple
declarative style using auditable macros (CBMC), both far simpler than the implementations.
The Hoare-style correctness specifications in HOL Light have been carefully audited and are
extensively used for numerous other assembly kernels in s2n-bignum, without infidelities
being detected. For CBMC, modular proof means that a wrong specification on a callee will
typically cause the caller's proof to fail. Top-level CBMC specifications don't use magic
constants; all buffer length values are defined in [params.h](mlkem/src/params.h) and
easily auditable to align with FIPS 203.

Residual risks remain: the constant-time specification style in HOL Light/s2n-bignum could
fail to detect a practically relevant class of variable-time execution; a misconfiguration
of CBMC could cause the implicit expectation of memory- and type-safety being included in
the CBMC specifications not to hold; or a CBMC proof could incorrectly disable a safety
check.

**Potential improvements.**
- Derive the CBMC configuration from a machine- and human-readable source documenting
  the desired configuration options and their meaning. (TODO: Add issue)
- Provide a document which explains the specification style for correctness and constant-time
  properties in HOL Light. (TODO: Ref tracking issue)

### A4. Specification consistency

Do the individual specifications compose to a coherent claim about the whole system? The
risks are that a contract assumed during proof differs from the contract that is proved,
that a contract assumed during proof is never proved, or that the bridge between the
CBMC and HOL Light verification stacks introduces an inconsistency.

#### CBMC compositionality

When CBMC proves a function F using the contract of a callee G (via `USE_FUNCTION_CONTRACTS`),
it assumes G's contract as an axiom. The contract it assumes must be the same contract that
is proved for G in G's own proof. In mlkem-native, this is enforced structurally: each
function has a single contract written at its declaration site, and CBMC uses that same
contract both when proving the function and when assuming it as a callee. There is no
mechanism by which the "assumed" and "proved" versions can diverge.

This structural guarantee is reinforced by the
[check-contracts](scripts/check-contracts) script, which looks for CBMC functions with a
contract but no proof. Additionally, bounds assertions in CBMC specifications are mirrored
by executable checks at the beginning and end of the respective function, so that if a
function is not covered by CBMC -- erroneously or deliberately -- tests in debug mode can
still catch gross mismatches between what the caller provides/assumes and what the callee
assumes/provides.

Residual risks remain: a function's proof could be present but not run in CI (e.g., due to
a CI configuration error), or a function's proof could be absent but
[check-contracts](scripts/check-contracts) could fail to detect it due to a bug or
misconfiguration.

#### The bridge between CBMC and HOL Light

Where C code calls into assembly, the assembly function has both a HOL Light specification
(proved against the object code) and a CBMC contract (assumed by CBMC when proving the C
caller). These two specifications are written in different languages and maintained
independently. Their consistency is checked manually, as follows, requiring that:

- The CBMC contract on the assembly function reflects aspects of the HOL Light
  specification relevant to memory- and type-safety (typically bounds assumptions
  and memory footprint).

Both the HOL Light proofs and the CBMC contracts contain comments of the form
`/* This must be kept in sync with the HOL Light specification in ... */`
(or vice versa) to flag the manual dependency.

**Example.** For the AArch64 NTT:

- HOL Light proves: if input coefficients satisfy `abs(ival(x i)) <= 8191`, then output
  satisfies `abs(ival zi) <= 23594` and `ival zi ≡ forward_ntt(ival ∘ x)(i) (mod 3329)`.
  We provide an exact description of the mathematical function being computed by the
  AArch64 NTT assembly kernel.
- The CBMC contract on `mlk_ntt_asm` simplifies this to bounds assertions
  `requires(array_abs_bound(p, 0, MLKEM_N, 8192))`
  and `ensures(array_abs_bound(p, 0, MLKEM_N, 23595))`.

**Mitigations.**
The "keep in sync" comments in both the CBMC and the HOL Light specifications provide a
review checkpoint. The full test suite exercises the native backend code paths, catching
gross mismatches. Furthermore, CBMC proves the C wrapper correct *assuming* the assembly
contract, so an inconsistency between the wrapper's precondition and the assembly's
precondition would typically cause the wrapper proof to fail.

Despite these safeguards, residual risks remain. A transcription error could cause the CBMC
contract on the assembly function to fail to faithfully reflect the HOL Light specification
-- e.g., an off-by-one in a bound, a missing aliasing constraint, or a wrong constant. An
ABI mismatch could cause the C calling convention assumed by the CBMC contract to differ
from the actual register/stack layout used by the assembly. And a semantic gap between the
CBMC contract language and HOL Light's logic -- for example, differing signed vs. unsigned
interpretation of bounds -- could cause the bridge to be unsound.

**Potential improvements.**
- Establish a machine-checked link between the HOL Light specifications and the CBMC
  contracts. (TODO: Ref tracking issue)

---

## Gap B: Do the formal models match the actual systems?

### B1. ISA model fidelity (assembly)

The HOL Light ISA models (`arm.ml`, `x86.ml`) and their decoders (`decode.ml`) are
hand-written from the ARM and Intel architecture reference manuals. Errors in those
references, misunderstandings, or transcription mistakes could silently invalidate proofs.

**Mitigation: co-simulation testing.** s2n-bignum's CI includes a co-simulation test
(`simulator.ml` + `simulator.c`) that repeatedly picks random instruction encodings and
random register/flag states, decodes them, executes them both symbolically through the
formal model and natively on real hardware, and compares results. This exercises both the
ISA semantics and the decoder. It in CI and covers all register-to-register instruction
forms with randomized operands, as well as memory-accessing instructions via dedicated
harnesses for various addressing modes.

Where instructions have genuinely underspecified behavior -- for example, `IMUL` sets flags
differently on different x86 microarchitectures -- the s2n-bignum model reflects this
nondeterminism, and proofs are valid regardless of which behavior the hardware exhibits.

mlkem-native does not run co-simulation testing itself; it relies on s2n-bignum's CI to
validate the ISA models. Since mlkem-native uses the same ISA models and decoder as
s2n-bignum (via the shared HOL Light infrastructure), this is appropriate -- but it means
that mlkem-native's assurance for ISA model fidelity is inherited, not independently
established.

See [^s2n-bignum-soundness] for full details.

### B2. Object code verification and reassembly (assembly)

The HOL Light proofs work at the level of object-code byte sequences, not the assembly source.
This takes the assembler out of the TCB of the proof. However, two risks remain.

**ELF loader.** An OCaml ELF loader extracts the `.text` section (and, where applicable,
the `.rodata` section) from each object file for verification. If it extracts the wrong
bytes, the proof applies to different code than what runs in production. This risk is
mitigated by the fact that the proof engineer must know the exact byte sequence to write
the proof, so loader errors would typically cause proof failure rather than a silently
wrong proof. Additionally, function-level random testing compares assembly outputs against
C reference implementations, catching gross mismatches.

See [^s2n-bignum-soundness] for further details on the ELF loader.

**Reassembly risk.** When mlkem-native's `.S` files are assembled on a different system --
whether by mlkem-native's own build, by a downstream consumer such as AWS-LC, or by a
cross-compilation toolchain -- there is currently no systematic check that the resulting
object code matches the bytes the proofs were verified against.
Assembler bugs, version differences, or different assembler dialects can and
do produce different object code (for example, it has been observed that some x86
compilers swap operands of AVX2 `VPADD` instruction to reduce code size).

**Potential improvements.**
- Provide a tool to consumers for checking that assembly/compilation results contain
  the expected byte code for all native functions covered by HOL Light proofs.  (TODO: Ref tracking issue)

### B3. Model omissions (assembly)

The formal HOL Light ISA model is a sequential, user-mode, single-core model. It does not model:

- **Caches, TLBs, or memory ordering.** Irrelevant for single-threaded sequential code,
  but means the model says nothing about concurrent use.
- **Interrupts and exceptions.** The proof assumes uninterrupted execution. In practice,
  interrupts are transparent to user-mode code on both x86 and ARM.
- **Virtual memory and page faults.** The model uses a flat address space. Page faults
  are transparent provided the OS has mapped the relevant pages.
- **Speculative execution.** The model is non-speculative. Side-channel risks from
  speculative execution (Spectre-class) are not addressed by the current proofs.
- **System registers and privilege levels.** The model covers user-mode general-purpose
  and SIMD registers only.

These omissions are standard for this class of verification and are not expected to affect
functional correctness of sequential user-mode code.

See [^s2n-bignum-soundness] for further discussion.

### B4. Hardware not implementing the ISA

The formal proofs assume that the physical hardware faithfully implements the ISA as
specified in the architecture reference manuals. In reality, this assumption can fail in
multiple ways:

- **CPU errata (systematic bugs).** CPUs can have bugs. Vendors published errata lists documenting
  cases where specific instructions behave incorrectly under specific conditions. If an mlkem-native
  assembly routine triggers such an erratum, the proof's guarantee does not hold on affected hardware.

- **Transient physical faults.** Cosmic rays, voltage fluctuations, thermal effects, or
  aging can cause transient bit flips in registers, memory, or logic. Such faults can
  silently corrupt computation. ECC memory mitigates memory-level faults but does not
  protect registers or execution logic.

- **Fault injection (deliberate attacks).** An adversary with physical access can
  deliberately induce faults (voltage glitching, EM injection, laser fault injection) to
  corrupt cryptographic computations. This is a well-studied attack vector against
  cryptographic implementations, particularly in embedded and smartcard contexts.

**Mitigations.**
- Co-simulation testing (see above) exercises the actual hardware and would detect systematic
  errata for the specific instructions and operand patterns tested. However, coverage is
  inherently limited by the limited scope of the CI.
- Transient faults and fault injection are entirely outside the scope of the formal model
  and the current proofs. No countermeasures (e.g., redundant computation, fault detection
  checks) are implemented.

**Residual risks.** This is a fundamental limitation shared by all software-level formal
verification: the proofs reason about an idealized machine, not the physical device. For
high-assurance deployments in physically hostile environments, additional countermeasures
at the hardware or protocol level would be needed.

### B5. C semantics model fidelity

CBMC gives meaning to C by translating C source into an internal representation and then into SMT formulas. Bugs in
CBMC's C-to-SMT translation could cause it to miss undefined behavior and to accept incorrect code; this has happened in
the past. However, CBMC is a mature, widely-used tool with an active community and extensive test suite, and
mlkem-native uses the latest CBMC version.

Also, the C language has many conformant implementations. For example, the width of pointer types could be
8/16/32/64-bit (or even larger on capability based architectures). CBMC models types and other implementation-defined
behavior (such as struct padding) following the host system's C compiler. At present, mlkem-native's CBMC proofs are
only run on 64-bit systems, and hence do not transfer to 16-bit or 32-bit systems. To mitigate this, the full functional
test suite (KAT, ACVP, unit tests) is run on a large variety of platforms and C compilers, covering 16-bit, 32-bit, and
64-bit C implementations. Moreover, mlkem-native uses fixed-width integer types (e.g. uint16_t) to reduce the risk of
semantic differences across compilers, and targets the initial C90 revision of C, which is expected to have more mature
compiler support and be less prone to modeling errors than newer language features.

Also, CBMC's memory model uses a flat, object-based representation with practically infinite space for local variables,
that is strictly more abstract than the target platform's memory layout. Concretely, for example, C imposes no limit on
the stack size (there is not even a notion of stack in C), but real systems do -- stack overflows are out of scope of
mlkem-native's CBMC proofs. To address this, mlkem-native's header provides constants for its memory usage that are
tested in CI to be accurate, reducing the risk of out-of-memory conditions such as stack overflows.

Finally, a compiler bug could lead to wrong object code being generated from correct C code, and proofs on outdated C
code could undermine the formal model. To guard against this, mlkem-native's CBMC proofs are run on every CI commit,
providing continuous regression testing and preventing proofs from getting out of date.

**Potential improvements.**
- Run CBMC proofs against 16-bit and 32-bit C compilers.

---

## Gap C: Is the proof infrastructure sound?

There is risk that the formal statements made about the formal model are proved,
yet not true, because of an unsoundness in the underlying proof infrastructure.

### C1. HOL Light kernel and OCaml runtime

HOL Light has a small trusted kernel (~400 lines of OCaml) implementing 10 primitive
inference rules and 3 axioms. All theorems must be constructed through this kernel (the
LCF architecture). No soundness bugs have been found since 2003.

Independent reassurance is provided by [^Candle][Candle] and [^HOLTrace].

See [^s2n-bignum-soundness] for full details.

### C2. CBMC & SMT solver trusted computing base

The CBMC trusted computing base is substantially larger than HOL Light's:

- **CBMC itself**: The C frontend, GOTO program transformation, and SMT encoding are all
  part of the TCB. Unlike HOL Light's LCF architecture, there is no small kernel through
  which all results must pass. A bug anywhere in the CBMC pipeline could produce a false
  "verified" result.
- **SMT solvers** (Z3, Bitwuzla): These are complex software systems. A solver bug
  directly compromises soundness. Unlike HOL Light's LCF architecture, where bugs in
  proof automation cannot compromise soundness, a solver bug in CBMC's backend directly
  invalidates the proof.
- **The C compiler used by CBMC**: CBMC uses a C preprocessor and parser; bugs in these
  components could affect the analysis.

**Mitigations.**

- CBMC has been in development for more than 20 years and is widely used in industry (including
  at Amazon for AWS-LC and other projects).
- The SMT solvers are independently developed and extensively tested.
- mlkem-native's proofs are run continuously in CI, providing regression testing.

**Residual risks.** The CBMC TCB is orders of magnitude larger than HOL Light's. There is
no independent proof-checking mechanism analogous to Candle or HOLTrace. The soundness
guarantee for the C proofs is therefore fundamentally weaker than for the assembly proofs.

**Potential improvements**:
- Systematically introduce redundancy by employing more than one SMT solver backend
  for CBMC functions.

<!--- bibliography --->
[^CBMC]: Amazon Web Services Diffblue: C Bounded Model Checker, [https://github.com/diffblue/cbmc](https://github.com/diffblue/cbmc)
[^Candle]: Oskar Abrahamsson, Magnus O. Myreen, Ramana Kumar, Thomas Sewell: Candle: Formally Verified clone of HOL-Light, [https://cakeml.org/candle/](https://cakeml.org/candle/)
[^FIPS203]: National Institute of Standards and Technology: FIPS 203 Module-Lattice-Based Key-Encapsulation Mechanism Standard, [https://csrc.nist.gov/pubs/fips/203/final](https://csrc.nist.gov/pubs/fips/203/final)
[^HOL-Light]: John Harrison: HOL-Light Theorem Prover, [https://hol-light.github.io/](https://hol-light.github.io/)
[^HOLTrace]: Daniel J. Bernstein: HOLTrace: A collection of tools for processing traces of a HOL Light session, [https://holtrace.cr.yp.to/](https://holtrace.cr.yp.to/)
[^s2n-bignum]: Amazon Web Services: s2n-bignum: Library of formally assembly kernels verified in HOL-Light, [https://github.com/awslabs/s2n-bignum/](https://github.com/awslabs/s2n-bignum/)
[^s2n-bignum-soundness]: Amazon Web Services: s2n-bignum soundness documentation, [https://github.com/awslabs/s2n-bignum/blob/main/doc/s2n_bignum_soundness.md](https://github.com/awslabs/s2n-bignum/blob/main/doc/s2n_bignum_soundness.md)
