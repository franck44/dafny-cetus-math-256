
module math_64 {
  // Definition of 2^n (Power2(m))
  import opened Std.Arithmetic.Power2
  import opened Std.BoundedInts
  import opened MathBVHelpers
  import opened MaxConstants

  const LO_64_MASK: bv128 := 0xffffffffffffffff
  const HI_64_MASK: bv128 := 0xffffffffffffffff0000000000000000

  /**
    * Adds two uint64 numbers with wrapping on overflow.
    *
    * @param n1 The first uint64 operand
    * @param n2 The second uint64 operand  
    * @returns The result of (n1 + n2) modulo 2^64
    *
    * @ensures The result is always equal to (n1 + n2) % 2^64
    */
  function wrapping_add(n1: uint64, n2: uint64): (r: uint64)
    ensures r as int == (n1 as int + n2 as int) % Pow2(64)
  {
    var (sum, _) := overflowing_add(n1, n2);
    sum
  }

  /**
    * Adds two uint64 numbers and returns both the result and whether an overflow occurred.
    *
    * @param n1 The first uint64 operand
    * @param n2 The second uint64 operand  
    * @returns A tuple containing:
    *          - The lower 64 bits of the sum as uint64
    *          - A boolean indicating whether an overflow occurred (true if overflow)
    *
    * @ensures The overflow flag is true iff n1 + n2 > MAX_U64
    * @ensures The result value always equals (n1 + n2) % 2^64 
    */
  function overflowing_add(n1: uint64, n2: uint64): (r: (uint64, bool) )
    ensures r.1 <==> (n1 as uint128) + (n2 as uint128) > MAX_U64 as uint128
    ensures r.0 as int == (n1 as int + n2 as int) % Pow2(64)
  {
    Lemma2To256();
    var sum := (n1 as uint128) + (n2 as uint128);
    if (sum > (MAX_U64 as uint128)) then
      LO_64_MASK_is_Modulo_Pow2(sum);
      (((sum as bv128 & LO_64_MASK) as uint64), true)
    else
      ((sum as uint64), false)
  }

  /**
    * Subtracts two uint64 numbers with wrapping on underflow.
    *
    * @param n1 The first uint64 operand (minuend)
    * @param n2 The second uint64 operand (subtrahend)
    * @returns The result of (n1 - n2) modulo 2^64
    *
    * @ensures The result is always equal to (n1 - n2) % 2^64
    */
  function wrapping_sub(n1: uint64, n2: uint64): (r: uint64)
    ensures r as int == (n1 as int - n2 as int) % TWO_TO_THE_64
  {
    var (result, _) := overflowing_sub(n1, n2);
    result
  }

  /**
    * Subtracts two uint64 numbers and returns both the result and whether an overflow occurred.
    *
    * @param n1 The first uint64 operand 
    * @param n2 The second uint64 operand 
    * @returns A tuple containing:
    *          - The result of subtraction (n1 - n2) modulo 2^64 as uint64
    *          - A boolean indicating whether an underflow occurred (true if n1 < n2)
    *
    * @ensures The overflow flag is true iff n1 < n2
    * @ensures If no overflow, the result is exactly n1 - n2
    * @ensures If overflow occurs, the result wraps around by 2^64
    */
  function overflowing_sub(n1: uint64, n2: uint64): (r: (uint64, bool))
    ensures r.1 <==> n1 as int - n2 as int < 0
    ensures r.0 as int == (n1 as int - n2 as int) % TWO_TO_THE_64
  {
    if (n1 >= n2) then
      ((n1 - n2), false)
    else
      var k : uint64 := (MAX_U64 - n2 as int) as uint64;
      ((k + n1 + 1) as uint64, true)
  }

  /**
    * Multiplies two uint64 numbers with wrapping on overflow.
    *
    * @param n1 The first uint64 operand
    * @param n2 The second uint64 operand  
    * @returns The result of (n1 * n2) modulo 2^64
    *
    * @ensures The result is always equal to (n1 * n2) % 2^64
    */
  function wrapping_mul(n1: uint64, n2: uint64): uint64 {
    var (m, _) := overflowing_mul(n1, n2);
    m
  }

  /** 
    * Multiplies two uint64 numbers and returns both the result and whether an overflow occurred.
    *
    * @param n1 The first uint64 operand
    * @param n2 The second uint64 operand  
    * @returns A tuple containing:
    *          - The lower 64 bits of the product (n1 * n2) % 2^64 as uint64
    *          - A boolean indicating whether an overflow occurred (true if product >= 2^64)
    *
    * @ensures The result is always equal to (n1 * n2) % 2^64 
    * @ensures The overflow flag is true iff n1 as int * n2 as int >= 2^64
    */
  function overflowing_mul(n1: uint64, n2: uint64): (r: (uint64, bool))
    ensures r.0 as int == (n1 as int * n2 as int) % Pow2(64)
    ensures r.1 <==> (n1 as int * n2 as int) >= Pow2(64)
  {
    assert n1 as int * n2 as int < TWO_TO_THE_128 by {
      if n1 > 0 && n2 > 0 {
        Lemma2To256();
        Mul.LemmaMulStrictUpperBound(n1 as int,  Pow2(64), n2 as int, Pow2(64));
        Power.LemmaPowAdds(2, 64, 64);
      }
    }
    // m is provably a uint128 so no overflow in the bv128
    var m : uint128 := (n1 as uint128) * (n2 as uint128);
    LO_64_MASK_is_Modulo_Pow2(m);
    HI_16_MASK_and_non_zero_is_larger_than_pow2(m);
    (((m as bv128 & LO_64_MASK) as uint64), (m as bv128 & HI_64_MASK) > 0)
  }

  /**
    * Adds three uint64 numbers (with a carry bit) and returns the result and new carry.
    *
    * @param n1 The first uint64 operand
    * @param n2 The second uint64 operand
    * @param carry The carry bit (must be 0 or 1)
    * @returns A tuple containing:
    *          - The result of (n1 + n2 + carry) modulo 2^64 as uint64
    *          - The new carry bit (0 or 1)  
    *
    * @requires The input carry must be 0 or 1
    * @ensures The output carry is 0 or 1
    * @ensures The output carry is 1 iff the sum >= 2^64
    * @ensures The result is equal to (n1 + n2 + carry) % 2^64
    */
  function carry_add(n1: uint64, n2: uint64, carry: uint64): (r :(uint64, uint64))
    requires carry <= 1
    ensures r.1 <= 1
    ensures r.1 == 1 ==> (n1 as int) + (n2 as int) + (carry as int) >= Pow2(64)
    ensures r.0 as int == ((n1 as int) + (n2 as int) + (carry as int)) % Pow2(64)
  {
    Lemma2To256();
    var sum := (n1 as uint128) + (n2 as uint128) + (carry as uint128);
    if (sum as bv128 > LO_64_MASK) then
      LO_64_MASK_is_Modulo_Pow2(sum);
      (((sum as bv128 & LO_64_MASK) as uint64), 1)
    else
      ((sum as uint64), 0)
  }

  /**
    * Checks if adding two uint64 numbers would overflow.
    *
    * @param n1 The first uint64 operand
    * @param n2 The second uint64 operand
    * @returns A boolean indicating whether n1 + n2 would fit in a uint64
    * 
    * @ensures Returns true iff n1 + n2 <= MAX_U64 (no overflow would occur)
    */
  function add_check(n1: uint64, n2: uint64): (r: bool)
    ensures r <==> n1 as int + n2 as int <= MAX_U64
  {
    (MAX_U64 as uint64 - n1 >= n2)
  }

  //---------------------------------------------------------------------------
  //  The lemmas to help the proof.
  //---------------------------------------------------------------------------

  /**
    * Proves that applying the LO_64_MASK to a uint128 number performs 
    * the same operation as taking the number modulo 2^64.
    *
    * @param n The uint128 number to mask
    * @ensures The low 64 bits of n equal n modulo 2^64
    */
  lemma {:axiom} LO_64_MASK_is_Modulo_Pow2(n: uint128)
    // requires n as int > MAX_U64
    ensures ((n as bv128) & LO_64_MASK) as int == n as int % Pow2(64)

  /**
    * Proves that the high 64 bits of a uint128 are non-zero if and only if 
    * the number is greater than or equal to 2^64.
    *
    * @param m The uint128 number to check
    * @ensures The high 64 bits are non-zero iff m >= 2^64
    */
  lemma HI_16_MASK_and_non_zero_is_larger_than_pow2(m: uint128)
    ensures m as bv128 & HI_64_MASK > 0 <==> m as int >= Pow2(64)
  {
    Lemma2To256();
    // Use an axiom on the conversion from int to bv128
    as_bv128_as_uint128(m);
  }

}