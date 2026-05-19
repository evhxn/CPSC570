# Quantum Homework: Qiskit and PyZX

**CPSC 570: From Bugs to Proofs** · Chapman University · Spring 2026

---

## Setup

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install qiskit qiskit-aer pyzx matplotlib
```

Run each file:

```bash
python3 bell_qiskit.py
python3 bell_pyzx.py
```

---

## Part 1: Qiskit

### Q1: Bell-state circuit

The circuit applies H to qubit 0, then CNOT (control: 0, target: 1), then measures both qubits.

```
     ┌───┐     ┌─┐
q_0: ┤ H ├──■──┤M├───
     └───┘┌─┴─┐└╥┘┌─┐
q_1: ─────┤ X ├─╫─┤M├
          └───┘ ║ └╥┘
c: 2/═══════════╩══╩═
                0  1
{'11': 513, '00': 511}
```

H puts qubit 0 into the superposition `(|0⟩ + |1⟩) / √2`. The CNOT then entangles both qubits: when qubit 0 is `|0⟩` the target stays `|0⟩`, and when qubit 0 is `|1⟩` the target flips to `|1⟩`. The result is the Bell state `(|00⟩ + |11⟩) / √2`. Measuring collapses this uniformly to either `00` or `11`, so counts are split roughly 50/50 between those two outcomes and never show `01` or `10`.

---

### Q2: Phase-modified circuit

A Z gate is inserted on qubit 0 after the CNOT and before measurement.

```
     ┌───┐     ┌───┐┌─┐
q_0: ┤ H ├──■──┤ Z ├┤M├
     └───┘┌─┴─┐└┬─┬┘└╥┘
q_1: ─────┤ X ├─┤M├──╫─
          └───┘ └╥┘  ║
c: 2/════════════╩═══╩═
                 1   0
{'00': 520, '11': 504}
```

**1. Do the measurement counts change?**
No. The counts remain concentrated on `00` and `11` with roughly equal probability.

**2. What changed about the quantum state?**
The Z gate flips the phase of the `|1⟩` component on qubit 0, transforming the state from `(|00⟩ + |11⟩) / √2` to `(|00⟩ − |11⟩) / √2`. The minus sign is a relative phase difference between the two amplitudes.

**3. Why is this hidden from a single measurement basis?**
Computational-basis measurement only sees the squared magnitudes of the amplitudes. Both `+1/√2` and `−1/√2` have the same magnitude squared (`1/2`), so the Born-rule probabilities are identical. The relative phase is only observable if you measure in a different basis — for example, applying H gates before measuring would reveal the interference and produce distinguishable counts.

---

### Q3: Equivalent Bell circuit

The second circuit uses the identity `CNOT = (I ⊗ H) · CZ · (I ⊗ H)`, giving the decomposition H(q0), H(q1), CZ(q0,q1), H(q1).

```
     ┌───┐        ┌─┐
q_0: ┤ H ├─■──────┤M├───
     ├───┤ │ ┌───┐└╥┘┌─┐
q_1: ┤ H ├─■─┤ H ├─╫─┤M├
     └───┘   └───┘ ║ └╥┘
c: 2/══════════════╩══╩═
                   0  1
{'11': 520, '00': 504}
```

**Are simulator results enough to prove equivalence?**
No. Matching measurement counts in the computational basis only shows the same output *probabilities* in that one basis. As Q2 demonstrates, two circuits that differ by a global or relative phase can produce identical counts. Simulation gives statistical evidence, not a proof. A stronger claim of equivalence requires either a formal algebraic verification (showing the two unitary matrices are equal) or a tool like PyZX's `verify_equality`, which checks exact unitary equivalence up to global phase.

---

## Part 2: PyZX

### Q4: Bell circuit in PyZX

```
=== Original Bell circuit ===
Circuit(2 qubits, 0 bits, 2 gates)
qubits: 2
gates: 2
two-qubit gates: 1
```

The circuit is built with `add_gate("HAD", 0)` and `add_gate("CNOT", 0, 1)`, mirroring the Qiskit construction directly.

---

### Q5: Simplification

```
=== Original Bell circuit ===
Circuit(2 qubits, 0 bits, 2 gates)
qubits: 2
gates: 2
two-qubit gates: 1

=== Simplified Bell circuit ===
Circuit(2 qubits, 0 bits, 4 gates)
qubits: 2
gates: 4
two-qubit gates: 1
```

The simplified circuit extracted by `full_reduce` + `extract_circuit` is: HAD(q1), HAD(q0), CZ(q0,q1), HAD(q1) — equivalent to the alternative Bell decomposition from Q3. The gate count goes from 2 to 4 because `full_reduce` works in the ZX-calculus (where CNOT and HAD are not primitive), and the extracted circuit uses a CZ-based decomposition that happens to require more named gates even though it is unitarily identical. The two-qubit gate count stays at 1. PyZX's simplification is aimed at minimizing T-count (for fault-tolerant computation), not total gate count, so a larger Clifford circuit after simplification is expected for this already-simple input.

---

### Q6: Equivalence checking

```
original equivalent to simplified:
True

original equivalent to phase-modified:
False
```

**Original vs. simplified — `True`:**
`verify_equality` confirms the two circuits implement the same unitary matrix (up to global phase). Mathematically this means: for every possible input state `|ψ⟩`, both circuits produce the same output state. The ZX-calculus rewrite rules used by `full_reduce` are all sound — they preserve the semantics of the diagram — so equivalence is guaranteed by construction, and `verify_equality` provides an independent matrix-level confirmation.

**Original vs. phase-modified — `False`:**
The Bell circuit produces `(|00⟩ + |11⟩) / √2`; the phase-modified circuit produces `(|00⟩ − |11⟩) / √2`. These are distinct quantum states and distinct unitary operations. Despite producing identical computational-basis measurement distributions (as seen in Q2), they are not the same circuit — the relative phase difference is physically meaningful and would produce different outcomes if measured in the Hadamard basis. PyZX correctly distinguishes them because it compares full unitary matrices, not just sampling statistics.

---

## Files

| File | Description |
|------|-------------|
| `bell_qiskit.py` | Q1–Q3: Bell circuit, phase-modified circuit, equivalent decomposition |
| `bell_pyzx.py` | Q4–Q6: PyZX circuit, simplification, equivalence checking |
| `README.md` | This write-up |

---

## Author

**Ethan** · B.S. Computer Science, Chapman University '26
