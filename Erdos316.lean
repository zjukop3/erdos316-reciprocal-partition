/-!
# Erdős Problem 316

Can every set A (with 0,1 not in A, reciprocal sum < 2) be partitioned
into two parts each with reciprocal sum < 1?

Answer: NO. The set A = {2, 3, 4, 5, 6, 7, 10, 11, 13, 14, 15} is a
counterexample. We verify computationally that:
  - 0 ∉ A, 1 ∉ A
  - ∑ 1/n ≈ 1.998 < 2
  - For every subset B of A, either ∑_{n∈B} 1/n ≥ 1 or ∑_{n∈A\B} 1/n ≥ 1

Using LCM-scaled integer arithmetic (LCM = 60060) for efficient computation.

See: https://www.erdosproblems.com/forum/thread/316
-/

namespace Erdos316

/-- LCM of elements of A. -/
def lcmA : Nat := 60060

/-- Scaled reciprocal sum: ∑ (LCM/n) for n in list. Equals LCM * ∑(1/n). -/
def scaledSum : List Nat → Nat
  | [] => 0
  | n :: ns => lcmA / n + scaledSum ns

/-- Set difference: elements of A not in B. -/
def setDiff : List Nat → List Nat → List Nat
  | [], _ => []
  | n :: ns, B => if B.contains n then setDiff ns B else n :: setDiff ns B

/-- All subsequences (subsets preserving order). -/
def allSubsets : List Nat → List (List Nat)
  | [] => [[]]
  | n :: ns =>
    let rest := allSubsets ns
    rest.map (fun s => n :: s) ++ rest

/-- The counterexample set. -/
def A : List Nat := [2, 3, 4, 5, 6, 7, 10, 11, 13, 14, 15]

/-- Threshold: LCM * 1 = 60060. sum ≥ 1 ↔ scaledSum ≥ 60060. -/
def threshold : Nat := lcmA

/-- Upper bound: LCM * 2 = 120120. sum < 2 ↔ scaledSum < 120120. -/
def upperBound : Nat := 2 * lcmA

/-- Main theorem: A is a counterexample to Erdős 316. -/
theorem erdos_316 :
    0 ∉ A ∧ 1 ∉ A ∧ scaledSum A < upperBound ∧
    ∀ B ∈ allSubsets A,
      threshold ≤ scaledSum B ∨ threshold ≤ scaledSum (setDiff A B) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide +kernel
  · decide +kernel

end Erdos316
