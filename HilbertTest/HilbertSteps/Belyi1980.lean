import HilbertTest.Belyi1980.Polynomial

/-!
Hilbert-facing proof targets for the checked polynomial layer of Belyi's 1980
paper.
-/

namespace HilbertTest
namespace HilbertSteps
namespace Belyi1980

open Real

theorem hilbert_auxPolynomial_zero
    {m n : Nat} (hm : 0 < m) :
    Belyi1980.auxPolynomial m n 0 = 0 := by
  exact Belyi1980.auxPolynomial_zero hm

theorem hilbert_auxPolynomial_one
    {m n : Nat} (hn : 0 < n) :
    Belyi1980.auxPolynomial m n 1 = 0 := by
  exact Belyi1980.auxPolynomial_one hn

theorem hilbert_normalizedAuxPolynomial_zero
    {m n : Nat} (hm : 0 < m) :
    Belyi1980.normalizedAuxPolynomial m n 0 = 0 := by
  exact Belyi1980.normalizedAuxPolynomial_zero hm

theorem hilbert_normalizedAuxPolynomial_one
    {m n : Nat} (hn : 0 < n) :
    Belyi1980.normalizedAuxPolynomial m n 1 = 0 := by
  exact Belyi1980.normalizedAuxPolynomial_one hn

theorem hilbert_hasDerivAt_auxPolynomial
    (m n : Nat) (x : Real) :
    HasDerivAt (fun y : Real => Belyi1980.auxPolynomial m n y)
      ((m : Real) * x ^ (m - 1) * (1 - x) ^ n -
        (n : Real) * x ^ m * (1 - x) ^ (n - 1)) x := by
  exact Belyi1980.hasDerivAt_auxPolynomial m n x

theorem hilbert_auxDerivativeValue_factor
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) (x : Real) :
    Belyi1980.auxDerivativeValue m n x =
      x ^ (m - 1) * (1 - x) ^ (n - 1) *
        ((m : Real) * (1 - x) - (n : Real) * x) := by
  exact Belyi1980.auxDerivativeValue_factor hm hn x

theorem hilbert_auxDerivativeValue_eq_zero_iff
    {m n : Nat} (hm : 1 < m) (hn : 1 < n) (x : Real) :
    Belyi1980.auxDerivativeValue m n x = 0 ↔
      x = 0 ∨ x = 1 ∨ x = (m : Real) / ((m + n : Nat) : Real) := by
  exact Belyi1980.auxDerivativeValue_eq_zero_iff hm hn x

theorem hilbert_middle_linear_factor_zero
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    (m : Real) * (1 - (m : Real) / ((m + n : Nat) : Real)) -
        (n : Real) * ((m : Real) / ((m + n : Nat) : Real)) = 0 := by
  exact Belyi1980.middle_linear_factor_zero hm hn

theorem hilbert_derivativeValue_auxPolynomial_middle_eq_zero
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    (m : Real) * ((m : Real) / ((m + n : Nat) : Real)) ^ (m - 1) *
          (1 - (m : Real) / ((m + n : Nat) : Real)) ^ n -
        (n : Real) * ((m : Real) / ((m + n : Nat) : Real)) ^ m *
          (1 - (m : Real) / ((m + n : Nat) : Real)) ^ (n - 1) = 0 := by
  exact Belyi1980.derivativeValue_auxPolynomial_middle_eq_zero hm hn

theorem hilbert_hasDerivAt_auxPolynomial_middle_zero
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    HasDerivAt (fun y : Real => Belyi1980.auxPolynomial m n y) 0
      ((m : Real) / ((m + n : Nat) : Real)) := by
  exact Belyi1980.hasDerivAt_auxPolynomial_middle_zero hm hn

theorem hilbert_hasDerivAt_normalizedAuxPolynomial_middle_zero
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    HasDerivAt (fun y : Real => Belyi1980.normalizedAuxPolynomial m n y) 0
      ((m : Real) / ((m + n : Nat) : Real)) := by
  exact Belyi1980.hasDerivAt_normalizedAuxPolynomial_middle_zero hm hn

theorem hilbert_middle_mem_unit_interval
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    0 < (m : Real) / ((m + n : Nat) : Real) ∧
      (m : Real) / ((m + n : Nat) : Real) < 1 := by
  exact Belyi1980.middle_mem_unit_interval hm hn

theorem hilbert_one_sub_middle_eq_right_ratio
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    1 - (m : Real) / ((m + n : Nat) : Real) =
      (n : Real) / ((m + n : Nat) : Real) := by
  exact Belyi1980.one_sub_middle_eq_right_ratio hm hn

theorem hilbert_normalizedAuxPolynomial_middle_eq_one
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    Belyi1980.normalizedAuxPolynomial m n
      ((m : Real) / ((m + n : Nat) : Real)) = 1 := by
  exact Belyi1980.normalizedAuxPolynomial_middle_eq_one hm hn

theorem hilbert_auxPolynomial_middle_eq_power_product
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    Belyi1980.auxPolynomial m n ((m : Real) / ((m + n : Nat) : Real)) =
      ((m : Real) / ((m + n : Nat) : Real)) ^ m *
        ((n : Real) / ((m + n : Nat) : Real)) ^ n := by
  exact Belyi1980.auxPolynomial_middle_eq_power_product hm hn

theorem hilbert_normalizedAuxPolynomial_basic_data
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    Belyi1980.normalizedAuxPolynomial m n 0 = 0 ∧
      Belyi1980.normalizedAuxPolynomial m n 1 = 0 ∧
      HasDerivAt (fun y : Real => Belyi1980.normalizedAuxPolynomial m n y) 0
        ((m : Real) / ((m + n : Nat) : Real)) ∧
      Belyi1980.normalizedAuxPolynomial m n
        ((m : Real) / ((m + n : Nat) : Real)) = 1 := by
  exact Belyi1980.normalizedAuxPolynomial_basic_data hm hn

theorem hilbert_middle_power_product_pos
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    0 <
      ((m : Real) / ((m + n : Nat) : Real)) ^ m *
        ((n : Real) / ((m + n : Nat) : Real)) ^ n := by
  exact Belyi1980.middle_power_product_pos hm hn

theorem hilbert_middle_power_product_le_quarter
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    ((m : Real) / ((m + n : Nat) : Real)) ^ m *
        ((n : Real) / ((m + n : Nat) : Real)) ^ n <= 1 / 4 := by
  exact Belyi1980.middle_power_product_le_quarter hm hn

theorem hilbert_auxPolynomial_middle_pos
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    0 < Belyi1980.auxPolynomial m n ((m : Real) / ((m + n : Nat) : Real)) := by
  exact Belyi1980.auxPolynomial_middle_pos hm hn

theorem hilbert_auxPolynomial_middle_le_quarter
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    Belyi1980.auxPolynomial m n ((m : Real) / ((m + n : Nat) : Real)) <= 1 / 4 := by
  exact Belyi1980.auxPolynomial_middle_le_quarter hm hn

end Belyi1980
end HilbertSteps
end HilbertTest
