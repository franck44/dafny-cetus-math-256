/**
  *  Provides a formal proof of the correctness of the `checked_shlw` function,
  *  which performs a left shift operation on a 256-bit unsigned integer.
  */
module math_u256 {

  // Use some Dafny standard libraries for definitions & proofs

  // Definition of 2^n (Power2(m))
  import opened Std.Arithmetic.Power2
  // TWO_TO_THE_n
  import opened Std.BoundedInts
  import opened MathBVHelpers

  // define the u256 type
  newtype u256 = x: int | 0 <= x < TWO_TO_THE_256

  /**
    * Performs a left shift by 64 bits on a 256-bit unsigned integer.
    * The function checks for overflow by testing if the input is larger than or equal to 2^192.
    * If overflow occurs, returns (0, true), otherwise returns (n << 64, false).
    *
    * @param n A 256-bit unsigned integer to be shifted left
    * @returns A tuple (r.0, r.1) where:
    *   - r.0 is the shifted value if no overflow, 0 otherwise
    *   - r.1 is true iff n * 2^64 >= 2^256
    */
  function checked_shlw(n: bv256): (r: (bv256, bool))
    // false indicates no overflow and n << 64 is equal to n as nat * Pow2(64)
    ensures !r.1 ==> r.0 as nat == n as nat * Pow2(64) < Pow2(256)
    // true indicates overflow if we compute n >> 64 as n as nat * Pow2(64)
    // does not fit within a bv256
    ensures r.1 ==> r.0 == 0 && n as nat * Pow2(64) >= Pow2(256)
    // Summary as an iff condition
    ensures !r.1 <==>  n as nat * Pow2(64) < Pow2(256)
  {
    var mask := (1 as bv256 << 192 as bv8);
    calc {
      mask as nat;
      (1 as bv256 << 192 as bv8) as nat;
      { Bv2562Pow2(192 as bv8); }
      Pow2(192);
    }
    if (n >= mask) then
      assert n as nat >= Pow2(192);
      LemmaHelperShiftLeft64LargerThanPow2_192(n);
      assert n as nat * Pow2(64) >= Pow2(256);
      (0, true)
    else
      assert n as nat < Pow2(192);
      LemmaHelperShiftLeft64LessThanPow2_192(n);
      assert  (n << 64) as nat == n as nat * Pow2(64) < Pow2(256);
      (n << 64, false)
  }

  /**
    * Calculates the division of a by b  and rounds up if enabled.
    *
    * @param a The dividend (numerator)
    * @param b The divisor (denominator), must be positive
    * @returns a/b, rounded up if round_up is `true` and num mod denom is non zero.
    */
  function div_roundup(num:u256, denom: u256, round_up: bool): (r: u256)
    requires denom != 0
    ensures !round_up || num % denom == 0 ==> r == num / denom
    ensures round_up && num % denom != 0 ==> r as nat == (num as nat / denom as nat + 1) < TWO_TO_THE_256
  {
    var p := num /denom;
    assert p * denom <= num;
    assert p as nat * denom as nat < TWO_TO_THE_256;
    if round_up && (p * denom != num) then
      // no overflow here. This assert is not really need as the result is u256
      // and Dafny flags overflows if the result does not fit in the type.
      assert p as nat + 1 < TWO_TO_THE_256;
      p + 1
    else
      p
  }
}