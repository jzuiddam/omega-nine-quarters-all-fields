/-
Copyright 2026 Jeroen Zuiddam. Licensed under the Apache License, Version 2.0 (see LICENSE).
-/
import OAI.LinearAlgebra.MatrixMultiplication.AllFields.Main

/-!
Axiom and non-vacuity checks.  Run with `lake env lean Checks/Axioms.lean`.
Every `#print axioms` should report `[propext, Classical.choice, Quot.sound]`.
-/

open OAI

#check @OAI.MatrixMultiplication.omega_le_nine_quarters_all_fields
#print axioms OAI.MatrixMultiplication.omega_le_nine_quarters_all_fields
#check @OAI.MatrixMultiplication.admissibleExponent_nine_quarters_all_fields
#print axioms OAI.MatrixMultiplication.admissibleExponent_nine_quarters_all_fields
#print axioms OAI.MatrixMultiplication.matrix_multiplication_cost_le_all_fields
#check @OAI.MatrixMultiplication.AuxiliarySeparation.omega_le_nine_quarters
#print axioms OAI.MatrixMultiplication.AuxiliarySeparation.omega_le_nine_quarters
#check @OAI.MatrixMultiplication.AuxiliarySeparation.complex_omega_le_nine_quarters
#print axioms OAI.MatrixMultiplication.AuxiliarySeparation.complex_omega_le_nine_quarters

-- The admissible set over any field is bounded below (by 2), so `omega F` is a genuine infimum.
example (F : Type*) [Field F] :
    BddBelow {τ : ℝ | MatrixMultiplication.Arithmetic.AdmissibleExponent F τ} :=
  MatrixMultiplication.Arithmetic.admissibleExponent_bddBelow F

-- `9/4 + δ` is admissible for every `δ > 0`.
example (F : Type*) [Field F] (δ : ℝ) (hδ : 0 < δ) :
    MatrixMultiplication.Arithmetic.AdmissibleExponent F (9/4 + δ) :=
  (MatrixMultiplication.admissibleExponent_nine_quarters_all_fields F).mono (by linarith)

-- Concrete fields, including characteristic 5, where the paper's period `L = 5M` is impossible.
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
example : MatrixMultiplication.Arithmetic.omega (ZMod 5) ≤ 9/4 :=
  MatrixMultiplication.omega_le_nine_quarters_all_fields (ZMod 5)
instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
example : MatrixMultiplication.Arithmetic.omega (ZMod 2) ≤ 9/4 :=
  MatrixMultiplication.omega_le_nine_quarters_all_fields (ZMod 2)
example : MatrixMultiplication.Arithmetic.omega ℚ ≤ 9/4 :=
  MatrixMultiplication.omega_le_nine_quarters_all_fields ℚ
-- A field in a higher universe: the theorem is universe-polymorphic.
example : MatrixMultiplication.Arithmetic.omega (ULift.{3} ℚ) ≤ 9/4 :=
  MatrixMultiplication.omega_le_nine_quarters_all_fields (ULift.{3} ℚ)
