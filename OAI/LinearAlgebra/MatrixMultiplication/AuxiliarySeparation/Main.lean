/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Main.lean`, by Jeroen Zuiddam,
2026: Theorem 1.1 and `omega_le_nine_quarters` stated over an algebraically closed field `K`;
`complex_omega_le_nine_quarters` is now the instance `K = ℂ`; `ℂ` replaced by a field `K`;
`[IsAlgClosed K]` is assumed by the declarations that use it.
-/
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.Exponent
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankBound
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.RankLowerBound
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Bounds
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Floor
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace OAI

variable {K : Type} [Field K]

/-!
# Matrix multiplication via auxiliary separation and polynomial multiplication

Theorem 1.1 gives a uniform arithmetic-operation bound for square matrix
multiplication over an algebraically closed field `K` of any characteristic
(in particular `K = ℂ`), and consequently an upper bound of `9/4` on its
exponent.  The two conclusions are stated separately in the existing arithmetic
model.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- Theorem 1.1: for every positive exponent slack, one constant bounds the cost
of correct matrix multiplication programs over `K` at every positive size. -/
theorem matrix_multiplication_cost_le [IsAlgClosed K] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : Arithmetic.MatrixAlgorithm K n n n,
        P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ ((9 : ℝ) / 4 + ε) :=
  arithmeticComplexity_of_exactRankExponent_le exactRankExponent_le_nine_quarters ε hε

/-- The arithmetic matrix multiplication exponent of an algebraically closed
field is at most `9/4`. -/
theorem omega_le_nine_quarters [IsAlgClosed K] : Arithmetic.omega K ≤ (9 : ℝ) / 4 :=
  omega_le_exactRankExponent.trans exactRankExponent_le_nine_quarters

/-- The complex case. -/
theorem complex_omega_le_nine_quarters : Arithmetic.omega ℂ ≤ (9 : ℝ) / 4 :=
  omega_le_nine_quarters

end MatrixMultiplication.AuxiliarySeparation

end OAI
